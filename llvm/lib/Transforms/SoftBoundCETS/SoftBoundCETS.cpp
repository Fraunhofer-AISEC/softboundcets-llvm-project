//=== SoftBoundCETS/SoftBoundCETS.cpp --*- C++ -*=====///
// Pointer based Spatial and Temporal Memory Safety Pass
// Copyright (c) 2014 Santosh Nagarakatte, Milo M. K. Martin. All rights
// reserved.
//
// Developed by: Santosh Nagarakatte,
//               Department of Computer Science,
//               Rutgers University
//               http://www.cs.rutgers.edu/~santosh.nagarakatte/softbound/
//
//               in collaboration with
//               Milo Martin, Jianzhou Zhao, Steve Zdancewic
//               University of Pennsylvania
//
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to
// deal with the Software without restriction, including without limitation the
// rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
// sell copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
//   1. Redistributions of source code must retain the above copyright notice,
//      this list of conditions and the following disclaimers.

//   2. Redistributions in binary form must reproduce the above copyright
//      notice, this list of conditions and the following disclaimers in the
//      documentation and/or other materials provided with the distribution.

//   3. Neither the names of Santosh Nagarakatte, Milo M. K. Martin,
//      Jianzhou Zhao, Steve Zdancewic, University of Pennsylvania,
//      Rutgers University, nor the names of its contributors may be
//      used to endorse or promote products derived from this Software
//      without specific prior written permission.

// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.  IN NO EVENT SHALL THE
// CONTRIBUTORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
// FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS
// WITH THE SOFTWARE.
//===---------------------------------------------------------------------===//

#include "llvm-c/Transforms/AggressiveInstCombine.h"
#include "llvm/ADT/TinyPtrVector.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Metadata.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/VirtualFileSystem.h"
#include "llvm/Transforms/AggressiveInstCombine/AggressiveInstCombine.h"
#include "llvm/Transforms/IPO.h"
#include "llvm/Transforms/IPO/AlwaysInliner.h"
#include "llvm/Transforms/IPO/Inliner.h"
#include "llvm/Transforms/InstCombine/InstCombine.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"
#include "llvm/Transforms/Utils/ValueMapper.h"
#include <cstddef>
#include <regex>

#include "FixByValAttributes.h"
#include "SoftBoundCETS.h"
#include "Utils.h"

static cl::opt<bool> ClEliminateStructChecks(
    "eliminate_struct_checks",
    cl::desc("don't perform any spatial checking for structure accesses"),
    cl::init(false));

static cl::opt<bool> ClSimpleMetadataMode(
    "simple_metadata_mode",
    cl::desc("use wrapper functions for metadata loads instead of allocas"),
    cl::init(false));

static cl::opt<bool>
    ClDisableSpatialCheckOpt("disable_spatial_check_opt",
                             cl::desc("disable spatial check optimizations"),
                             cl::init(false));

static cl::opt<bool>
    ClDisableTemporalCheckOpt("disable_temporal_check_opt",
                              cl::desc("disable temporal check optimizations"),
                              cl::init(false));

static cl::opt<bool>
    ClSpatialSafety("softboundcets-spatial-safety",
                    cl::desc("Enable instrumentation for spatial safety"),
                    cl::init(true));

static cl::opt<bool>
    ClTemporalSafety("softboundcets-temporal-safety",
                     cl::desc("Enable instrumentaion for temporal safety"),
                     cl::init(true));

static cl::opt<bool> ClAssociateMissingMetadata(
    "softboundcets-associate-missing-metadata",
    cl::desc(
        "Associate missing metadata for a value where is is missing (mostly "
        "due to incompleteness/errors in the SoftBoundCETS compiler pass)"),
    cl::init(false));

static cl::opt<bool> ClAssociateOmnivalidMetadataWhenMissing(
    "softboundcets-associate-omnivalid-metadata-when-missing",
    cl::desc("Associate omnivalid metadata for a value where is is missing "
             "(this has "
             "only an effect when ClAssociateMissingMetadata is true)"),
    cl::init(true));

static cl::opt<bool> ClExternalLibsAreInstrumented(
    "softboundcets-external-libs-are-instrumented",
    cl::desc("Assume external libraries are instrumented by SoftBoundCETS as "
             "well. This implies instrumenting calls to functions in external "
             "libraries."),
    cl::init(false));

static cl::opt<bool> ClMaximalCompatibilityWithExternalLibs(
    "softboundcets-maximal-compatibility-with-external-libs",
    cl::desc("Associate returned pointers of calls to external functions with "
             "omnivalid metadata. Has only an effect if "
             "ClExternalLibrariesAreInstrumented is false."),
    cl::init(true));

static cl::opt<bool> ClAssociateZeroInitializedGlobalsWithOmnivalidMetadata(
    "softboundcets-zeroinit-globals-omnivalid-metadata",
    cl::desc("Associate zeroinitialized globals with omnivalid metadata. "
             "This helps when the globals are instead initialized at runtime "
             "by external"
             "uninstrumented code, preventing false positives."),
    cl::init(true));

static cl::opt<bool> ClAssociateIntToPtrCastsWithOmnivalidMetadata(
    "softboundcets-int2ptr-casts-omnivalid-metadata",
    cl::desc("Associate Int to Ptr casts with omnivalid metadata. "
             "This helps for compatibility with (legacy) code."),
    cl::init(true));

static cl::opt<bool> ClAssociateVaargPointerWithOmnivalidMetadata(
    "softboundcets-vaarg-pointer-omnivalid-metadata",
    cl::desc("Associate pointers loaded from variadic arguments with omnivalid "
             "metadata. "
             "Until now, SBCETS has no concept how to deal with them."),
    cl::init(true));

static cl::opt<bool> ClCreateSecondaryShadowSpaceTriesWhenMissing(
    "softboundcets-create-secondary-tries",
    cl::desc(
        "Call to metadata shadowspace function which checks if the secondary "
        "tries is non-NULL, and if no, allocates the secondary trie."),
    cl::init(false));

static cl::opt<bool> ClIntraObjectBounds(
    "softboundcets-check-intra-object-bounds",
    cl::desc("Resize base and bound when taking a GEP of an aggregate value. "
             "This allows for detecting intra-object over- and underflows."),
    cl::init(false));

static cl::opt<std::string> ClPrintInstrumentedFunctions(
    "softboundcets-print-instrumented-functions",
    cl::desc("A comma-separated list of functions "
             "to be printed after instrumentation."),
    cl::init(""));
static cl::opt<bool> ClPrintAllInstrumentedFunctions(
    "softboundcets-print-all-instrumented-functions",
    cl::desc("Print all instrumented functions."), cl::init(false));

static cl::opt<bool>
    ClInlineRuntimeLibFunctions("softboundcets-inline-rtlib-functions",
                                cl::desc("Inline SoftBoundCETS runtime library "
                                         "functions into the main program."),
                                cl::init(false));

static cl::opt<bool>
    ClPropagateMetadataOnly("softboundcets_mdprop_only",
                            cl::desc("perform only metadata propagation"),
                            cl::init(false));

static cl::opt<bool> ClInsertCheckIntrinsics(
    "softboundcets_chk_intrinsic",
    cl::desc("insert intrinsics for spatial and temporal safety"),
    cl::init(false));

static cl::opt<bool> ClInsertSpatialLoadChecks(
    "softboundcets_spatial_safety_load_checks",
    cl::desc("introduce load dereference checks for spatial safety"),
    cl::init(true));

static cl::opt<bool> ClInsertSpatialStoreChecks(
    "softboundcets_spatial_safety_store_checks",
    cl::desc("introduce store dereference checks for spatial safety"),
    cl::init(true));

static cl::opt<bool> ClInsertTemporalLoadChecks(
    "softboundcets_temporal_load_checks",
    cl::desc("introduce temporal load dereference checks"), cl::init(true));

static cl::opt<bool> ClInsertTemporalStoreChecks(
    "softboundcets_temporal_store_checks",
    cl::desc("introduce temporal store dereference checks"), cl::init(true));

static cl::opt<bool> FUNCDOMTEMPORALCHECKOPT(
    "softboundcets_func_dom_temporal_check_opt",
    cl::desc(
        "eliminate function based redundant checks with dominator analysis"),
    cl::init(true));

static cl::opt<bool>
    STRUCTOPT("softboundcets_struct_opt",
              cl::desc("enable or disable structure optimization"),
              cl::init(true));

static cl::opt<bool> BOUNDSCHECKOPT(
    "softboundcets_bounds_check_opt",
    cl::desc("enable dominator based load dereference check elimination"),
    cl::init(true));

static cl::opt<bool> SHRINKBOUNDS(
    "softboundcets_shrink_bounds",
    cl::desc("enable shrinking bounds for the softboundboundcetswithss pass"),
    cl::init(false));

static cl::opt<bool>
    DISABLE_MEMCOPYCHECK("softboundcets_disable_memcopy_check",
                         cl::desc("disable check memcopy calls"),
                         cl::init(false));

static cl::opt<bool>
    GLOBALCONSTANTOPT("softboundcets_global_const_opt",
                      cl::desc("global constant expressions are not checked"),
                      cl::init(false));

static cl::opt<bool> CALLCHECKS("softboundcets_call_checks",
                                cl::desc("introduce call checks"),
                                cl::init(true));

static cl::opt<bool>
    INDIRECTCALLCHECKS("softboundcets_indirect_call_checks",
                       cl::desc("introduce indirect call checks"),
                       cl::init(false));

static cl::opt<bool> OPAQUECALLS(
    "softboundcets_opaque_calls",
    cl::desc("consider all calls as opaque for func_dom_check_elimination"),
    cl::init(true));

static cl::opt<bool> TEMPORALBOUNDSCHECKOPT(
    "softboundcets_temporal_bounds_check_opt",
    cl::desc("enable or disable temporal dominator based check elimination"),
    cl::init(false));

static cl::opt<bool> STACKTEMPORALCHECKOPT(
    "softboundcets_stack_temporal_check_opt",
    cl::desc("eliminate temporal checks for stack variables"), cl::init(true));

static cl::opt<bool> GLOBALTEMPORALCHECKOPT(
    "softboundcets_global_temporal_check_opt",
    cl::desc("eliminate temporal checks for global variables"), cl::init(true));

static cl::opt<bool> BBDOMTEMPORALCHECKOPT(
    "softboundcets_bb_dom_temporal_check_opt",
    cl::desc("eliminate redundant checks in the basic block"), cl::init(true));

static cl::opt<bool> DISABLE_MEMCOPY_METADATA_COPIES(
    "softboundcets_disable_memcpy_metadata_copies",
    cl::desc("disable metadata copies with memcopy"), cl::init(false));

#if 0
static cl::opt<bool>
unsafe_byval_opt
("unsafe_byval_opt",
 cl::desc("Unbound byval attributed pointers so that check always succeeds"),
 cl::init(false));
#endif

const char kSoftBoundCETSCtorName[] = "__softboundcets_ctor";
static const unsigned kSoftBoundCETSCtorPriority = 0;
const char kSoftBoundCETSInitializerName[] = "__softboundcets_init";
const char kSoftBoundCETSGlobalsInitializerName[] =
    "__softboundcets_init_globals";
const char kSoftBoundCETSWrapMainFnName[] = "__softboundcets_wrap_main";
const char kSoftBoundCETSRealMainFnName[] = "__softboundcets_real_main";
const char kSoftBoundCETSSpatialLoadDereferenceCheckFnName[] =
    "__softboundcets_spatial_load_dereference_check";
const char kSoftBoundCETSSpatialStoreDereferenceCheckFnName[] =
    "__softboundcets_spatial_store_dereference_check";
const char kSoftBoundCETSTemporalLoadDereferenceCheckFnName[] =
    "__softboundcets_temporal_load_dereference_check";
const char kSoftBoundCETSTemporalStoreDereferenceCheckFnName[] =
    "__softboundcets_temporal_store_dereference_check";
const char kSoftBoundCETSMemcpyDereferenceCheckFnName[] =
    "__softboundcets_memcopy_check";
const char kSoftBoundCETSMemsetDereferenceCheckFnName[] =
    "__softboundcets_memset_check";
const char kSoftBoundCETSIntrospectMetadataFnName[] =
    "__softboundcets_introspect_metadata";
const char kSoftBoundCETSCopyMetadataFnName[] = "__softboundcets_copy_metadata";
const char kSoftBoundCETSGetGlobalLockFnName[] =
    "__softboundcets_get_global_lock";
const char kSoftBoundCETSLoadMetadataPtrFnName[] =
    "__softboundcets_shadowspace_metadata_ptr";
const char kSoftBoundCETSLoadMetadataPtrWithSecTriesFnName[] =
    "__softboundcets_shadowspace_metadata_ptr_create_secondary_tries";
const char kSoftBoundCETSLoadVectorMetadataPtrFnName[] =
    "__softboundcets_shadowspace_vector_metadata_ptr";
const char kSoftBoundCETSLoadMaskedVectorMetadataPtrFnName[] =
    "__softboundcets_shadowspace_masked_vector_metadata_ptr";
const char kSoftBoundCETSLoadMetadataBaseFnName[] =
    "__softboundcets_metadata_load_base";
const char kSoftBoundCETSLoadMetadataBoundFnName[] =
    "__softboundcets_metadata_load_bound";
const char kSoftBoundCETSLoadMetadataKeyFnName[] =
    "__softboundcets_metadata_load_key";
const char kSoftBoundCETSLoadMetadataLockFnName[] =
    "__softboundcets_metadata_load_lock";

const char kSoftBoundCETSLoadVectorMetadataBaseFnName[] =
    "__softboundcets_metadata_load_vector_base";
const char kSoftBoundCETSLoadVectorMetadataBoundFnName[] =
    "__softboundcets_metadata_load_vector_bound";
const char kSoftBoundCETSLoadVectorMetadataKeyFnName[] =
    "__softboundcets_metadata_load_vector_key";
const char kSoftBoundCETSLoadVectorMetadataLockFnName[] =
    "__softboundcets_metadata_load_vector_lock";
const char kSoftBoundCETSMaskedLoadVectorMetadataBaseFnName[] =
    "__softboundcets_metadata_masked_load_vector_base";
const char kSoftBoundCETSMaskedLoadVectorMetadataBoundFnName[] =
    "__softboundcets_metadata_masked_load_vector_bound";
const char kSoftBoundCETSMaskedLoadVectorMetadataKeyFnName[] =
    "__softboundcets_metadata_masked_load_vector_key";
const char kSoftBoundCETSMaskedLoadVectorMetadataLockFnName[] =
    "__softboundcets_metadata_masked_load_vector_lock";

const char kSoftBoundCETSStoreMetadataFnName[] =
    "__softboundcets_metadata_store";
const char kSoftBoundCETSStoreVectorMetadataFnName[] =
    "__softboundcets_metadata_store_vector";
const char kSoftBoundCETSAllocateStackLockAndKeyFnName[] =
    "__softboundcets_stack_memory_allocation";
const char kSoftBoundCETSDeallocateStackLockAndKeyFnName[] =
    "__softboundcets_stack_memory_deallocation";
const char kSoftBoundCETSCallDereferenceCheckFnName[] =
    "__softboundcets_spatial_call_dereference_check";
const char kSoftBoundCETSAllocateShadowStackFnName[] =
    "__softboundcets_allocate_shadow_stack_space";
const char kSoftBoundCETSDeallocateShadowStackFnName[] =
    "__softboundcets_deallocate_shadow_stack_space";
const char kSoftBoundCETSLoadBaseShadowStackFnName[] =
    "__softboundcets_load_base_shadow_stack";
const char kSoftBoundCETSLoadBoundShadowStackFnName[] =
    "__softboundcets_load_bound_shadow_stack";
const char kSoftBoundCETSStoreMetadataShadowStackFnName[] =
    "__softboundcets_store_metadata_shadow_stack";
const char kSoftBoundCETSLoadKeyShadowStackFnName[] =
    "__softboundcets_load_key_shadow_stack";
const char kSoftBoundCETSLoadLockShadowStackFnName[] =
    "__softboundcets_load_lock_shadow_stack";
const char kSoftBoundCETSLoadShadowStackMetadataPtrFnName[] =
    "__softboundcets_shadow_stack_metadata_ptr";

// #define SOFTBOUNDCETS_CHK_INTRINSIC 1

char SoftBoundCETSPass::ID = 0;

#ifdef SOFTBOUNDCETS_EP_LTO

static RegisterStandardPasses SoftBoundCETSLTO(
    PassManagerBuilder::EP_FullLinkTimeOptimizationLast,
    [](const PassManagerBuilder &Builder, legacy::PassManagerBase &PM) {
      if (ClInlineRuntimeLibFunctions) {
        PM.add(createAlwaysInlinerLegacyPass());
      }
      PM.add(new FixByValAttributesPass());
      PM.add(new SoftBoundCETSPass());
      PM.add(createAggressiveInstCombinerPass());
      PM.add(createInstructionCombiningPass());
      PM.add(createGlobalOptimizerPass());
      PM.add(createGlobalDCEPass());
      PM.add(createInstructionCombiningPass());
      if (ClInlineRuntimeLibFunctions)
        PM.add(createAlwaysInlinerLegacyPass());
    });

static RegisterStandardPasses SoftBoundCETSLTO0(
    PassManagerBuilder::EP_EnabledOnOptLevel0,
    [](const PassManagerBuilder &Builder, legacy::PassManagerBase &PM) {
      PM.add(new FixByValAttributesPass());
      PM.add(new SoftBoundCETSPass());
    });

#endif

#ifdef SOFTBOUNDCETS_EP_OPT_LAST

static RegisterStandardPasses SoftBoundCETS(
    PassManagerBuilder::EP_OptimizerLast,
    [](const PassManagerBuilder &Builder, legacy::PassManagerBase &PM) {
      PM.add(new FixByValAttributesPass());
      PM.add(new SoftBoundCETSPass());
    });

static RegisterStandardPasses SoftBoundCETS0(
    PassManagerBuilder::EP_EnabledOnOptLevel0,
    [](const PassManagerBuilder &Builder, legacy::PassManagerBase &PM) {
      PM.add(new FixByValAttributesPass());
      PM.add(new SoftBoundCETSPass());
    });

#endif

StringMap<bool> SoftBoundCETSPass::MFunctionWrappersAvailable = {
    {"system", true},
    {"setreuid", true},
    {"mkstemp", true},
    {"getrlimit", true},
    {"setrlimit", true},
    {"fread", true},
    {"mkdir", true},
    {"chroot", true},
    {"rmdir", true},
    {"stat", true},
    {"fputc", true},
    {"fileno", true},
    {"fgetc", true},
    {"strncmp", true},
    {"fwrite", true},
    {"atof", true},
    {"feof", true},
    {"remove", true},
    {"tmpfile", true},
    {"ferror", true},
    {"ftell", true},
    {"fstat", true},
    {"fflush", true},
    {"fputs", true},
    {"fopen", true},
    {"fdopen", true},
    {"fseek", true},
    {"ftruncate", true},
    {"popen", true},
    {"fclose", true},
    {"pclose", true},
    {"rewind", true},
    {"readdir", true},
    {"opendir", true},
    {"closedir", true},
    {"rename", true},
    {"getcwd", true},
    {"chown", true},
    {"chdir", true},
    {"strcmp", true},
    {"strcasecmp", true},
    {"strncasecmp", true},
    {"strlen", true},
    {"strpbrk", true},
    {"gets", true},
    {"fgets", true},
    {"perror", true},
    {"strspn", true},
    {"strcspn", true},
    {"memcmp", true},
    {"memchr", true},
    {"rindex", true},
    {"strtoul", true},
    {"strtod", true},
    {"strtol", true},
    {"strchr", true},
    {"strrchr", true},
    {"strcpy", true},
    {"atoi", true},
    {"strtok", true},
    {"strdup", true},
    {"strcat", true},
    {"strncat", true},
    {"strncpy", true},
    {"strstr", true},
    {"signal", true},
    {"atol", true},
    {"realloc", true},
    {"calloc", true},
    {"malloc", true},
    {"mmap", true},

    {"times", true},
    {"strftime", true},
    {"localtime", true},
    {"time", true},
    {"free", true},
    {"ctime", true},
    {"setbuf", true},
    {"getenv", true},
    {"atexit", true},
    {"strerror", true},
    {"unlink", true},
    // TODO[orthen]: fix wrapper to check for arguments as functions with same
    // name can have different declarations
    // {"open", true},
    {"read", true},
    {"write", true},
    {"gettimeofday", true},
    {"select", true},
    {"__errno_location", true},
    {"__ctype_b_loc", true},
    {"__ctype_toupper_loc", true},
    {"__ctype_tolower_loc", true},
    {"qsort", true},
    {"puts", true},
    {"setlocale", true},
    // string.h wrappers
    {"__mempcpy", true},
    {"__stpcpy", true},
    {"__stpncpy", true},
    {"basename", true},
    {"explicit_bzero", true},
    {"memccpy", true},
    {"memfrob", true},
    {"memmem", true},
    {"memmove", true},
    {"memset", true},
    {"rawmemchr", true},
    {"stpncpy", true},
    {"strcasestr", true},
    {"strcoll", true},
    {"strcoll_l", true},
    {"strerror_l", true},
    {"strfry", true},
    {"strnlen", true},
    {"strsep", true},
    {"strsignal", true},
    {"strtok_r", true},
    {"strverscmp", true},
    {"strxfrm", true},
    {"strxfrm_l", true},
    // strings.h wrappers
    {"bcmp", true},
    {"bcopy", true},
    {"bzero", true},
    {"index", true},
    {"strcasecmp_l", true},
    {"strncasecmp_l", true},
    // stdio.h wrappers
    {"__asprintf", true},
    {"__overflow", true},
    {"__uflow", true},
    {"asprintf", true},
    {"clearerr", true},
    {"clearerr_unlocked", true},
    {"ctermid", true},
    {"cuserid", true},
    {"dprintf", true},
    {"feof_unlocked", true},
    {"ferror_unlocked", true},
    {"fflush_unlocked", true},
    {"fgetc_unlocked", true},
    {"fgetpos", true},
    {"fgetpos64", true},
    {"fgets_unlocked", true},
    {"fileno_unlocked", true},
    {"flockfile", true},
    {"fmemopen", true},
    {"fopen64", true},
    {"fopencookie", true},
    {"fprintf", true},
    {"fputc_unlocked", true},
    {"fputs_unlocked", true},
    {"freopen", true},
    {"freopen64", true},
    {"fscanf", true},
    {"fseeko64", true},
    {"fsetpos", true},
    {"fsetpos64", true},
    {"ftello", true},
    {"ftello64", true},
    {"ftrylockfile", true},
    {"funlockfile", true},
    {"fwrite_unlocked", true},
    {"getc", true},
    {"getc_unlocked", true},
    {"getdelim", true},
    {"getline", true},
    {"getw", true},
    {"obstack_printf", true},
    {"obstack_vprintf", true},
    {"open_memstream", true},
    {"printf", true},
    {"putc", true},
    {"putc_unlocked", true},
    {"putw", true},
    {"renameat2", true},
    {"scanf", true},
    {"setbuffer", true},
    {"setlinebuf", true},
    {"setvbuf", true},
    {"snprintf", true},
    {"sprintf", true},
    {"sscanf", true},
    {"tempnam", true},
    {"tmpfile64", true},
    {"tmpnam", true},
    {"tmpnam_r", true},
    {"vasprintf", true},
    {"vdprintf", true},
    {"vfprintf", true},
    {"vfscanf", true},
    {"vprintf", true},
    {"vscanf", true},
    {"vsnprintf", true},
    {"vsprintf", true},
    {"vsscanf", true},
    {"wcscpy", true},
    // Wrappers for unistd.h
    {"access", true},
    {"brk", true},
    {"confstr", true},
    {"copy_file_range", true},
    // {"crypt", true}, TODO: The wrapper did not compile
    {"eaccess", true},
    {"euidaccess", true},
    // {"execl", true},
    // {"execle", true},
    // {"execlp", true},
    {"execv", true},
    {"execve", true},
    {"execveat", true},
    {"execvp", true},
    {"execvpe", true},
    {"faccessat", true},
    {"fexecve", true},
    {"get_current_dir_name", true},
    {"getdomainname", true},
    {"getgroups", true},
    {"gethostname", true},
    {"getlogin", true},
    {"getlogin_r", true},
    {"getpass", true},
    {"getresgid", true},
    {"getresuid", true},
    {"getusershell", true},
    {"getwd", true},
    {"lchown", true},
    {"link", true},
    {"pipe", true},
    {"pipe2", true},
    {"pread", true},
    {"pread64", true},
    {"profil", true},
    {"pwrite", true},
    {"pwrite64", true},
    {"readlink", true},
    {"revoke", true},
    {"sbrk", true},
    {"setdomainname", true},
    {"sethostname", true},
    {"setlogin", true},
    {"swab", true},
    {"symlink", true},
    {"truncate", true},
    {"truncate64", true},
    {"ttyname", true},
    {"ttyname_r", true},
    {"acct", true},
    {"getentropy", true},
    // stdlib.h
    {"a64l", true},
    {"aligned_alloc", true},
    {"at_quick_exit", true},
    {"atoll", true},
    {"canonicalize_file_name", true},
    {"drand48_r", true},
    {"ecvt", true},
    {"ecvt_r", true},
    {"erand48", true},
    {"erand48_r", true},
    {"fcvt", true},
    {"fcvt_r", true},
    {"gcvt", true},
    {"getloadavg", true},
    {"getsubopt", true},
    {"initstate", true},
    {"initstate_r", true},
    {"jrand48", true},
    {"jrand48_r", true},
    {"l64a", true},
    {"lcong48", true},
    {"lcong48_r", true},
    {"lrand48_r", true},
    {"mblen", true},
    {"mbstowcs", true},
    {"mbtowc", true},
    {"mkostemp64", true},
    {"mkostemps", true},
    {"mkostemps64", true},
    {"mkstemps", true},
    {"mkstemps64", true},
    {"mktemp", true},
    {"mrand48_r", true},
    {"nrand48", true},
    {"nrand48_r", true},
    {"on_exit", true},
    {"posix_memalign", true},
    {"ptsname", true},
    {"ptsname_r", true},
    {"putenv", true},
    {"qecvt", true},
    {"qecvt_r", true},
    {"qfcvt", true},
    {"qfcvt_r", true},
    {"qgcvt", true},
    {"qsort_r", true},
    {"rand_r", true},
    {"random_r", true},
    {"realpath", true},
    {"secure_getenv", true},
    {"seed48", true},
    {"seed48_r", true},
    {"setstate", true},
    {"setstate_r", true},
    {"srand48_r", true},
    {"srandom_r", true},
    {"strfromd", true},
    {"strfromf", true},
    {"strfromf32", true},
    {"strfromf32x", true},
    {"strfromf64", true},
    {"strfromf64x", true},
    {"strfroml", true},
    {"strtod_l", true},
    {"strtof", true},
    {"strtof32", true},
    {"strtof32_l", true},
    {"strtof32x", true},
    {"strtof32x_l", true},
    {"strtof64", true},
    {"strtof64_l", true},
    {"strtof64x", true},
    {"strtof64x_l", true},
    {"strtof_l", true},
    {"strtol_l", true},
    {"strtold", true},
    {"strtold_l", true},
    {"strtoll", true},
    {"strtoll_l", true},
    {"strtoq", true},
    {"strtoul_l", true},
    {"strtoull", true},
    {"strtoull_l", true},
    {"strtouq", true},
    {"wcstombs", true},
    {"wctomb", true},
    {"reallocarray", true},
    // malloc.h
    {"malloc_info", true},
    {"malloc_usable_size", true},
    {"memalign", true},
    {"pvalloc", true},
    {"valloc", true},
};

StringMap<bool> SoftBoundCETSPass::MFunctionHasSoftboundCETSDefinition = {

    {"__softboundcets_intermediate", true},
    {"__softboundcets_dummy", true},
    {"__softboundcets_print_metadata", true},
    {"main", true},
    {kSoftBoundCETSCtorName, true},
    {kSoftBoundCETSIntrospectMetadataFnName, true},
    {kSoftBoundCETSCopyMetadataFnName, true},
    {kSoftBoundCETSAllocateShadowStackFnName, true},
    {kSoftBoundCETSDeallocateShadowStackFnName, true},

    {"__softboundcets_trie_allocate", true},
    {"__shrinkBounds", true},
    {kSoftBoundCETSMemcpyDereferenceCheckFnName, true},
    {kSoftBoundCETSMemsetDereferenceCheckFnName, true},

    {kSoftBoundCETSSpatialLoadDereferenceCheckFnName, true},
    {kSoftBoundCETSSpatialStoreDereferenceCheckFnName, true},
    {kSoftBoundCETSTemporalLoadDereferenceCheckFnName, true},
    {kSoftBoundCETSTemporalStoreDereferenceCheckFnName, true},
    {kSoftBoundCETSCallDereferenceCheckFnName, true},
    {kSoftBoundCETSAllocateStackLockAndKeyFnName, true},
    {"__softboundcets_memory_allocation", true},
    {kSoftBoundCETSGetGlobalLockFnName, true},
    {"__softboundcets_add_to_free_map", true},
    {"__softboundcets_check_remove_from_free_map", true},
    {"__softboundcets_allocation_secondary_trie_allocate", true},
    {"__softboundcets_allocation_secondary_trie_allocate_range", true},
    {"__softboundcets_allocate_lock_location", true},
    {"__softboundcets_memory_deallocation", true},
    {kSoftBoundCETSDeallocateStackLockAndKeyFnName, true},

    {kSoftBoundCETSStoreVectorMetadataFnName, true},
    {kSoftBoundCETSLoadMetadataLockFnName, true},
    {kSoftBoundCETSLoadMetadataKeyFnName, true},
    {kSoftBoundCETSLoadMetadataBaseFnName, true},
    {kSoftBoundCETSLoadMetadataBoundFnName, true},

    {kSoftBoundCETSLoadVectorMetadataLockFnName, true},
    {kSoftBoundCETSLoadVectorMetadataKeyFnName, true},
    {kSoftBoundCETSLoadVectorMetadataBaseFnName, true},
    {kSoftBoundCETSLoadVectorMetadataBoundFnName, true},
    {kSoftBoundCETSMaskedLoadVectorMetadataLockFnName, true},
    {kSoftBoundCETSMaskedLoadVectorMetadataKeyFnName, true},
    {kSoftBoundCETSMaskedLoadVectorMetadataBaseFnName, true},
    {kSoftBoundCETSMaskedLoadVectorMetadataBoundFnName, true},

    {kSoftBoundCETSStoreMetadataFnName, true},

    {kSoftBoundCETSCtorName, true},
    {kSoftBoundCETSInitializerName, true},
    {kSoftBoundCETSGlobalsInitializerName, true},
    {kSoftBoundCETSWrapMainFnName, true},
    {"__softboundcets_abort", true},
    {"__softboundcets_printf", true},
    {"__softboundcets_debug_printf", true},
    {"__softboundcets_error_printf", true},
    {"__softboundcets_log_message", true},
};

StringSet<> SoftBoundCETSPass::MIgnorableLLVMIntrinsics = {
   "llvm.lifetime.start.p0i8", "llvm.lifetime.end.p0i8"};

//
// Method: getAssociateFuncLock()
//
// Description:
//
// This method looks up the "lock" for global variables associated
// with the function. Every will have a getGlobalLockAddr function
// inserted at the beginning which will serve as the lock for all the
// global variables used in the function.
//
//
// Inputs:
//
// Pointer_inst: An instruction that is manipulating a global pointer
// value.
//
// Return value:
//
// Returns the "lock associated with the function. Should never return
// NULL.
//

// Method: initializeInitFunctions()
//
// Description: This function declares our runtime's initialization functions.
//
// Input:
//
// M: Module to insert the function declarations into.
void SoftBoundCETSPass::initializeInitFunctions(Module &M) {

  auto &C = M.getContext();
  auto *VoidTy = Type::getVoidTy(C);
  auto *Int8Ty = Type::getInt8Ty(C);
  auto *Int32Ty = Type::getInt32Ty(C);
  auto *Int8PtrTy = PointerType::getUnqual(Int8Ty);
  auto *Int8PtrPtrTy = PointerType::getUnqual(Int8PtrTy);

  M.getOrInsertFunction(kSoftBoundCETSInitializerName, VoidTy);

  M.getOrInsertFunction(kSoftBoundCETSWrapMainFnName, Int32Ty, Int32Ty,
                        Int8PtrPtrTy, Int8PtrPtrTy);
}

// Method: initializeDereferenceCheckHandlers()
//
// Description: This function declares our dereference check handlers.
//
// Input:
//
// M: Module to insert the function declarations into.
void SoftBoundCETSPass::initializeDereferenceCheckHandlers(Module &M) {

  auto &C = M.getContext();
  Type *VoidTy = Type::getVoidTy(C);
  Type *VoidPtrTy = PointerType::getUnqual(Type::getInt8Ty(C));
  Type *SizeTy;
  if (m_is_64_bit) {
    SizeTy = Type::getInt64Ty(C);
  } else {
    SizeTy = Type::getInt32Ty(C);
  }

  if (ClSpatialSafety) {

    SpatialLoadDereferenceCheckFn =
        M.getOrInsertFunction(kSoftBoundCETSSpatialLoadDereferenceCheckFnName,
                              VoidTy, VoidPtrTy, VoidPtrTy, VoidPtrTy, SizeTy);

    SpatialStoreDereferenceCheckFn =
        M.getOrInsertFunction(kSoftBoundCETSSpatialStoreDereferenceCheckFnName,
                              VoidTy, VoidPtrTy, VoidPtrTy, VoidPtrTy, SizeTy);

    CallDereferenceCheckFn =
        M.getOrInsertFunction(kSoftBoundCETSCallDereferenceCheckFnName, VoidTy,
                              VoidPtrTy, VoidPtrTy, VoidPtrTy);
  }

  if (ClTemporalSafety) {

    TemporalLoadDereferenceCheckFn =
        M.getOrInsertFunction(kSoftBoundCETSTemporalLoadDereferenceCheckFnName,
                              VoidTy, MLockPtrTy, SizeTy);

    TemporalStoreDereferenceCheckFn =
        M.getOrInsertFunction(kSoftBoundCETSTemporalStoreDereferenceCheckFnName,
                              VoidTy, MLockPtrTy, SizeTy);
  }

  if (ClSpatialSafety && !ClTemporalSafety) {

    MemcpyDereferenceCheckFn = M.getOrInsertFunction(
        kSoftBoundCETSMemcpyDereferenceCheckFnName, VoidTy, VoidPtrTy,
        VoidPtrTy, SizeTy, VoidPtrTy, VoidPtrTy, VoidPtrTy, VoidPtrTy);

    MemsetDereferenceCheckFn =
        M.getOrInsertFunction(kSoftBoundCETSMemsetDereferenceCheckFnName,
                              VoidTy, VoidPtrTy, SizeTy, VoidPtrTy, VoidPtrTy);

  } else if (!ClSpatialSafety && ClTemporalSafety) {

    MemcpyDereferenceCheckFn = M.getOrInsertFunction(
        kSoftBoundCETSMemcpyDereferenceCheckFnName, VoidTy, VoidPtrTy,
        VoidPtrTy, SizeTy, SizeTy, MLockPtrTy, SizeTy, MLockPtrTy);

    MemsetDereferenceCheckFn =
        M.getOrInsertFunction(kSoftBoundCETSMemsetDereferenceCheckFnName,
                              VoidTy, VoidPtrTy, SizeTy, SizeTy, MLockPtrTy);

  } else if (ClSpatialSafety && ClTemporalSafety) {

    MemcpyDereferenceCheckFn = M.getOrInsertFunction(
        kSoftBoundCETSMemcpyDereferenceCheckFnName, VoidTy, VoidPtrTy,
        VoidPtrTy, SizeTy, VoidPtrTy, VoidPtrTy, VoidPtrTy, VoidPtrTy, SizeTy,
        MLockPtrTy, SizeTy, MLockPtrTy);

    MemsetDereferenceCheckFn = M.getOrInsertFunction(
        kSoftBoundCETSMemsetDereferenceCheckFnName, VoidTy, VoidPtrTy, SizeTy,
        VoidPtrTy, VoidPtrTy, MKeyTy, MLockPtrTy);
  }
}

// Method: initializeMetadataHandlers()
//
// Description: This function declares our metadata handlers.
//
// Input:
//
// M: Module to insert the function declarations into.
void SoftBoundCETSPass::initializeMetadataHandlers(Module &M) {

  auto &C = M.getContext();
  Type *VoidTy = Type::getVoidTy(C);
  Type *VoidPtrTy = PointerType::getUnqual(Type::getInt8Ty(C));

  Type *SizeTy;
  if (m_is_64_bit) {
    SizeTy = Type::getInt64Ty(C);
  } else {
    SizeTy = Type::getInt32Ty(C);
  }

  Type *LockPtrPtrTy = PointerType::getUnqual(MLockPtrTy);
  Type *SizePtrTy = PointerType::getUnqual(SizeTy);
  Type *Int32Ty = Type::getInt32Ty(C);
  Type *Int1Ty = Type::getInt1Ty(C);

  StructType *MetadataStruct =
      StructType::getTypeByName(C, "struct.__softboundcets_metadata_t");

  if (!MetadataStruct) {
    MetadataStruct = StructType::create(C, "struct.__softboundcets_metadata_t");

    if (ClSpatialSafety && !ClTemporalSafety) {
      MetadataStruct->setBody({MVoidPtrTy, MVoidPtrTy});
    } else if (!ClSpatialSafety && ClTemporalSafety) {
      MetadataStruct->setBody({MKeyTy, MLockPtrTy});
    } else if (ClSpatialSafety && ClTemporalSafety) {
      MetadataStruct->setBody({MVoidPtrTy, MVoidPtrTy, MKeyTy, MLockPtrTy});
    }
  }

  Type *MetadataStructPtrTy = PointerType::getUnqual(MetadataStruct);

  if (ClCreateSecondaryShadowSpaceTriesWhenMissing)
    LoadMetadataPtrFn =
        M.getOrInsertFunction(kSoftBoundCETSLoadMetadataPtrWithSecTriesFnName,
                              MetadataStructPtrTy, MVoidPtrTy);
  else
    LoadMetadataPtrFn = M.getOrInsertFunction(
        kSoftBoundCETSLoadMetadataPtrFnName, MetadataStructPtrTy, MVoidPtrTy);

  LoadVectorMetadataPtrFn =
      M.getOrInsertFunction(kSoftBoundCETSLoadVectorMetadataPtrFnName,
                            MetadataStructPtrTy, MVoidPtrTy, Int32Ty);

  LoadMaskedVectorMetadataPtrFn =
      M.getOrInsertFunction(kSoftBoundCETSLoadMaskedVectorMetadataPtrFnName,
                            MetadataStructPtrTy, MVoidPtrTy, Int32Ty, Int1Ty);

  IntrospectMetadataFn =
      M.getOrInsertFunction(kSoftBoundCETSIntrospectMetadataFnName, VoidTy,
                            VoidPtrTy, VoidPtrTy, Int32Ty);

  CopyMetadataFn = M.getOrInsertFunction(kSoftBoundCETSCopyMetadataFnName,
                                         VoidTy, VoidPtrTy, VoidPtrTy, SizeTy);

  GetGlobalLockFn =
      M.getOrInsertFunction(kSoftBoundCETSGetGlobalLockFnName, MLockPtrTy);

  // =======================================
  // shadow stack handlers
  AllocateShadowStackFn = M.getOrInsertFunction(
      kSoftBoundCETSAllocateShadowStackFnName, VoidTy, SizeTy);

  DeallocateShadowStackFn =
      M.getOrInsertFunction(kSoftBoundCETSDeallocateShadowStackFnName, VoidTy);

  LoadMetadataPtrShadowStackFn =
      M.getOrInsertFunction(kSoftBoundCETSLoadShadowStackMetadataPtrFnName,
                            MetadataStructPtrTy, MSizetTy);

  if (ClSpatialSafety && !ClTemporalSafety) {
    StoreMetadataShadowStackFn =
        M.getOrInsertFunction(kSoftBoundCETSStoreMetadataShadowStackFnName,
                              VoidTy, MVoidPtrTy, MVoidPtrTy, SizeTy);
  } else if (!ClSpatialSafety && ClTemporalSafety) {
    StoreMetadataShadowStackFn =
        M.getOrInsertFunction(kSoftBoundCETSStoreMetadataShadowStackFnName,
                              VoidTy, MKeyTy, MLockPtrTy, SizeTy);
  } else if (ClSpatialSafety && ClTemporalSafety) {
    StoreMetadataShadowStackFn = M.getOrInsertFunction(
        kSoftBoundCETSStoreMetadataShadowStackFnName, VoidTy, MVoidPtrTy,
        MVoidPtrTy, MKeyTy, MLockPtrTy, SizeTy);
  }

  // =======================================

  if (ClSpatialSafety) {
    LoadMetadataBaseFn = M.getOrInsertFunction(
        kSoftBoundCETSLoadMetadataBaseFnName, VoidPtrTy, VoidPtrTy);

    LoadMetadataBoundFn = M.getOrInsertFunction(
        kSoftBoundCETSLoadMetadataBoundFnName, VoidPtrTy, VoidPtrTy);

    LoadVectorMetadataBaseFn =
        M.getOrInsertFunction(kSoftBoundCETSLoadVectorMetadataBaseFnName,
                              VoidPtrTy, VoidPtrTy, Int32Ty);

    LoadVectorMetadataBoundFn =
        M.getOrInsertFunction(kSoftBoundCETSLoadVectorMetadataBoundFnName,
                              VoidPtrTy, VoidPtrTy, Int32Ty);
    MaskedLoadVectorMetadataBaseFn =
        M.getOrInsertFunction(kSoftBoundCETSMaskedLoadVectorMetadataBaseFnName,
                              VoidPtrTy, VoidPtrTy, Int32Ty, Int1Ty);

    MaskedLoadVectorMetadataBoundFn =
        M.getOrInsertFunction(kSoftBoundCETSMaskedLoadVectorMetadataBoundFnName,
                              VoidPtrTy, VoidPtrTy, Int32Ty, Int1Ty);

    LoadBaseShadowStackFn = M.getOrInsertFunction(
        kSoftBoundCETSLoadBaseShadowStackFnName, VoidPtrTy, SizeTy);

    LoadBoundShadowStackFn = M.getOrInsertFunction(
        kSoftBoundCETSLoadBoundShadowStackFnName, VoidPtrTy, SizeTy);
  }

  if (ClTemporalSafety) {

    AllocateStackLockAndKeyFn =
        M.getOrInsertFunction(kSoftBoundCETSAllocateStackLockAndKeyFnName,
                              VoidTy, LockPtrPtrTy, SizePtrTy);

    DeallocateStackLockAndKeyFn = M.getOrInsertFunction(
        kSoftBoundCETSDeallocateStackLockAndKeyFnName, VoidTy, SizeTy);

    LoadMetadataLockFn = M.getOrInsertFunction(
        kSoftBoundCETSLoadMetadataLockFnName, MLockPtrTy, VoidPtrTy);

    LoadMetadataKeyFn = M.getOrInsertFunction(
        kSoftBoundCETSLoadMetadataKeyFnName, MKeyTy, VoidPtrTy);

    LoadVectorMetadataLockFn =
        M.getOrInsertFunction(kSoftBoundCETSLoadVectorMetadataLockFnName,
                              MLockPtrTy, VoidPtrTy, Int32Ty);

    LoadVectorMetadataKeyFn = M.getOrInsertFunction(
        kSoftBoundCETSLoadVectorMetadataKeyFnName, MKeyTy, VoidPtrTy, Int32Ty);

    MaskedLoadVectorMetadataLockFn =
        M.getOrInsertFunction(kSoftBoundCETSMaskedLoadVectorMetadataLockFnName,
                              MLockPtrTy, VoidPtrTy, Int32Ty, Int1Ty);

    MaskedLoadVectorMetadataKeyFn =
        M.getOrInsertFunction(kSoftBoundCETSMaskedLoadVectorMetadataKeyFnName,
                              MKeyTy, VoidPtrTy, Int32Ty, Int1Ty);

    LoadKeyShadowStackFn = M.getOrInsertFunction(
        kSoftBoundCETSLoadKeyShadowStackFnName, SizeTy, SizeTy);

    LoadLockShadowStackFn = M.getOrInsertFunction(
        kSoftBoundCETSLoadLockShadowStackFnName, MLockPtrTy, SizeTy);
  }

  if (ClSpatialSafety && !ClTemporalSafety) {

    StoreMetadataFn =
        M.getOrInsertFunction(kSoftBoundCETSStoreMetadataFnName, VoidTy,
                              VoidPtrTy, VoidPtrTy, VoidPtrTy);

    StoreVectorMetadataFn =
        M.getOrInsertFunction(kSoftBoundCETSStoreVectorMetadataFnName, VoidTy,
                              VoidPtrTy, VoidPtrTy, VoidPtrTy, Int32Ty);

  } else if (!ClSpatialSafety && ClTemporalSafety) {

    StoreMetadataFn =
        M.getOrInsertFunction(kSoftBoundCETSStoreMetadataFnName, VoidTy,
                              VoidPtrTy, MKeyTy, MLockPtrTy);

    StoreVectorMetadataFn =
        M.getOrInsertFunction(kSoftBoundCETSStoreVectorMetadataFnName, VoidTy,
                              VoidPtrTy, SizeTy, MLockPtrTy, Int32Ty);

  } else if (ClSpatialSafety && ClTemporalSafety) {

    StoreMetadataFn = M.getOrInsertFunction(kSoftBoundCETSStoreMetadataFnName,
                                            VoidTy, VoidPtrTy, VoidPtrTy,
                                            VoidPtrTy, SizeTy, MLockPtrTy);

    StoreVectorMetadataFn = M.getOrInsertFunction(
        kSoftBoundCETSStoreVectorMetadataFnName, VoidTy, VoidPtrTy, VoidPtrTy,
        VoidPtrTy, SizeTy, MLockPtrTy, Int32Ty);
  }
}

// Method: initializeSoftBoundVariables()
//
// Description:
//
//
// Input:
//
//
void SoftBoundCETSPass::initializeSoftBoundVariables(Module &M) {

  auto &Ctxt = M.getContext();

  MVoidPtrTy = PointerType::getUnqual(Type::getInt8Ty(Ctxt));

  size_t InfBound;
  if (m_is_64_bit) {
    MSizetTy = Type::getInt64Ty(Ctxt);
  } else {
    MSizetTy = Type::getInt32Ty(Ctxt);
  }
  MArgNoTy = MSizetTy;
  MKeyTy = MSizetTy;

  if (m_is_64_bit) {
    InfBound = (size_t)pow(2, 48);
  } else {
    InfBound = (size_t)(2147483647);
  }

  Constant *InfiniteBound = ConstantInt::get(MSizetTy, InfBound, false);
  MInfiniteBoundPtr = ConstantExpr::getIntToPtr(InfiniteBound, MVoidPtrTy);

  MVoidNullPtr = ConstantPointerNull::get(MVoidPtrTy);

  MLockPtrTy = PointerType::getUnqual(MKeyTy);

  MConstantIntOne = ConstantInt::get(MSizetTy, 1);
  MConstantIntZero = ConstantInt::get(MSizetTy, 0);

  MGlobalLockOne = new GlobalVariable(
      M, MConstantIntOne->getType(), true, GlobalValue::InternalLinkage,
      MConstantIntOne, "__softboundcets_global_lock1");

  MGlobalLockOnes.insert(MGlobalLockOne);
}

void SoftBoundCETSPass::insertGlobalCtor(Module &M) {

  // Create a new constructor and add it to the global constructor list.
  auto *CtorFn = createSanitizerCtor(M, kSoftBoundCETSCtorName);
  appendToGlobalCtors(M, CtorFn, kSoftBoundCETSCtorPriority);

  // Before anything else, our constructor has to call the runtime initializer.
  auto *InitFn = M.getFunction(kSoftBoundCETSInitializerName);
  IRBuilder<> IRB(CtorFn->getEntryBlock().getTerminator());
  IRB.CreateCall(InitFn, {});
}

// Method: hasAllocaInst()
//
// Description:
//
// This function checks whether internal function has an alloca
// instruction in the function. This function is useful to determine
// whether we need to allocate a key and a lock for the function or
// not.
//
bool SoftBoundCETSPass::isAllocaPresent(Function *func) {

  for (Function::iterator bb_begin = func->begin(), bb_end = func->end();
       bb_begin != bb_end; ++bb_begin) {

    for (BasicBlock::iterator i_begin = bb_begin->begin(),
                              i_end = bb_begin->end();
         i_begin != i_end; ++i_begin) {

      Instruction *alloca_inst = dyn_cast<Instruction>(i_begin);

      if (isa<AllocaInst>(alloca_inst) &&
          MPresentInOriginal.count(alloca_inst)) {
        return true;
      }
    }
  }
  return false;
}

//
// Method: getFunctionKeyLock()
//
// Description:
//
// This function introduces a memory allocation call for allocating a
// new "key" and "lock" for the stack frames on function entry.  This
// function also stores the key and lock in the reference Value*
// arguments provided to the function.  Further, key and lock is
// allocated only when temporal checking is performed.
//
// Inputs:
//
// func: Function* of the function performing the allocation
// func_key: Value* & is the reference argument to return the key
// func_lock: Value* & is the reference_argument to return the lock
// func_xmm_lock: Value* & is the reference argument that will be
// eventually used to return the key and lock as wide parameters.
//

void SoftBoundCETSPass::getFunctionKeyLock(Function *func, Value *&func_key,
                                           Value *&func_lock,
                                           Value *&func_xmm_key_lock) {

  Instruction *func_alloca_inst = NULL;
  func_key = NULL;
  func_lock = NULL;
  func_xmm_key_lock = NULL;
  if (!ClTemporalSafety)
    return;

  if (!isAllocaPresent(func))
    return;

  func_alloca_inst = dyn_cast<Instruction>(func->begin()->begin());
  assert(func_alloca_inst && "func begin null?");
  addMemoryAllocationCall(func, func_key, func_lock, func_alloca_inst);

  return;
}

//
// Method: addMemoryAllocationCall()
//
// This function introduces a call to the C-handler function for
// allocating key and lock for stack frames. After the handler call,
// it performs the load of the key and the lock to use it as the
// metadata for pointers pointing to stack allocations in the
// function.
//
// Inputs:
//
// func: Function for which the key and the lock is being allocated
//
// ptr_key: Reference argument to return the key after the key and lock
// allocation
//
// ptr_lock: Reference argument to return the lock after
// the key and lock allocation
//
// insert_at: Instruction* before which the C-handler is introduced
//
// Outputs:
//
// A new key and lock is allocated by the C-handler and then returned
// via reference arguments that is used as key and lock for pointers
// pointing to stack allocations in the function.
//

void SoftBoundCETSPass::addMemoryAllocationCall(Function *func, Value *&ptr_key,
                                                Value *&ptr_lock,
                                                Instruction *insert_at) {
  SmallVector<Value *, 8> args;
  Instruction *first_inst_func = cast<Instruction>(func->begin()->begin());
  AllocaInst *lock_alloca =
      new AllocaInst(MLockPtrTy, 0, "lock_alloca", first_inst_func);
  AllocaInst *key_alloca = new AllocaInst(Type::getInt64Ty(func->getContext()),
                                          0, "key_alloca", first_inst_func);
  args.push_back(lock_alloca);
  args.push_back(key_alloca);

  Instruction *flc_call =
      CallInst::Create(AllocateStackLockAndKeyFn, args, "", first_inst_func);

  //
  // Load the key and lock from the reference arguments passed to the
  // C-handler
  //

  Instruction *next_inst = getNextInstruction(flc_call);
  Instruction *alloca_lock = new LoadInst(lock_alloca->getAllocatedType(),
                                          lock_alloca, "lock.load", next_inst);
  Instruction *alloca_key = new LoadInst(key_alloca->getAllocatedType(),
                                         key_alloca, "key.load", next_inst);

  ptr_key = alloca_key;
  ptr_lock = alloca_lock;
}

// Method: transformAndRedirectMain()
//
// Description:
//
// This method transforms the module's main function to always return int (users
// may declare main to return void) and always take three arguments (argument
// count, argument vector, and environment pointer; users may only declare a
// subset of these arguments or none at all). If the original main function
// returns void, the transformed main will always return zero. The transformed
// function is also renamed as specified in kSoftBoundCETSRealMainFnName.
//
// To create metadata for the arguments stored in the argument vector and the
// environment variables pointed to by the environment pointer, this method also
// redirects the execution of the transformed main function through a wrapper
// function. The wrapper is defined in the SoftBound+CETS runtime and named as
// specified in kSoftBoundCETSWrapMainFnName. For this redirection, the method
// inserts a new main function into the module that forwards all three arguments
// to the wrapper.
void SoftBoundCETSPass::transformAndRedirectMain(Module &M) {
  auto &C = M.getContext();
  Type *VoidTy = Type::getVoidTy(C);
  Type *Int8Ty = Type::getInt8Ty(C);
  Type *Int32Ty = Type::getInt32Ty(C);
  Type *Int8PtrTy = PointerType::getUnqual(Int8Ty);
  Type *Int8PtrPtrTy = PointerType::getUnqual(Int8PtrTy);

  // Transform main if we find it in the module.
  if (auto *OldMainFn = M.getFunction("main")) {

    // Create new main.
    auto *RealMainDeclaration = M.getFunction(kSoftBoundCETSRealMainFnName);
    auto *NewMainFn = Function::Create(
        FunctionType::get(Int32Ty, {Int32Ty, Int8PtrPtrTy, Int8PtrPtrTy},
                          false),
        GlobalValue::ExternalLinkage, kSoftBoundCETSRealMainFnName, &M);

    // Map new main's arguments to old main's arguments and additionally copy
    // over the names.
    ValueToValueMapTy VMap;
    for (auto OldMainArgIter = OldMainFn->arg_begin(),
              OldMainArgEnd = OldMainFn->arg_end(),
              NewMainArgIter = NewMainFn->arg_begin();
         OldMainArgIter != OldMainArgEnd; ++OldMainArgIter, ++NewMainArgIter) {
      assert(NewMainArgIter->getType() == OldMainArgIter->getType() &&
             "Arguments with differing types?");
      NewMainArgIter->setName(OldMainArgIter->getName());
      VMap[&*OldMainArgIter] = &*NewMainArgIter;
    }

    // Clone old main into new main.
    SmallVector<ReturnInst *, 8> Returns;
    CloneFunctionInto(NewMainFn, OldMainFn, VMap, true, Returns);

    // If old main returned void, replace all return instructions and return
    // zero by default.
    if (NewMainFn->getReturnType() != OldMainFn->getReturnType()) {
      assert(OldMainFn->getReturnType() == VoidTy &&
             "Main with non-standard return type?");
      auto *ReturnValue = Constant::getNullValue(Int32Ty);
      for (auto *RI : Returns) {
        ReturnInst::Create(C, ReturnValue, RI);
        RI->eraseFromParent();
      }
    }

    // Erase old main.
    OldMainFn->eraseFromParent();

    // Create new main that returns int and takes the argument count, argument
    // vector, and environment pointer as inputs.
    auto *MainFn = Function::Create(
        FunctionType::get(Int32Ty, {Int32Ty, Int8PtrPtrTy, Int8PtrPtrTy},
                          false),
        GlobalValue::ExternalLinkage, "main", &M);
    auto *MainFnBB = BasicBlock::Create(C, "", MainFn);

    // We forward all arguments to the wrapper.
    SmallVector<Value *, 3> WrapMainFnArgs;
    for (auto &Arg : MainFn->args())
      WrapMainFnArgs.push_back(&Arg);

    // Create a call to the wrapper and forward its return value.
    auto *WrapMainFn = M.getFunction(kSoftBoundCETSWrapMainFnName);
    auto *MainFnCI = CallInst::Create(WrapMainFn, WrapMainFnArgs, "", MainFnBB);
    ReturnInst::Create(C, MainFnCI, MainFnBB);

    if (RealMainDeclaration) {
      RealMainDeclaration->replaceAllUsesWith(NewMainFn);
    }
  }
}

bool SoftBoundCETSPass::isExternalDefinitelyInstrumentedFunction(
    const StringRef &Str) {
  return isFunctionNotToInstrument(Str) ||
         (MFunctionWrappersAvailable.count(Str) > 0);
}

//
// Method: isFuncDefSoftBound
//
// Description:
//
// This function checks if the input function name is a
// SoftBound/CETS defined function
//

bool SoftBoundCETSPass::isFunctionNotToInstrument(const StringRef &str) {

  // Is the function name in the above list?
  if (MFunctionHasSoftboundCETSDefinition.count(str) > 0) {
    return true;
  }

  // FIXME: handling new intrinsics which have isoc99 in their name
  if (str.find("isoc99") != std::string::npos) {
    return true;
  }

  if (str.find(kSoftBoundCETSRealMainFnName) == 0) {
    return false;
  }

  if (str.contains("softboundcets")) {
    return true;
  }

  // If the function is an llvm intrinsic, don't transform it
  if (str.find("llvm.") == 0) {
    return true;
  }

  return false;
}

bool SoftBoundCETSPass::isIgnorableLLVMIntrinsic(const StringRef &Str) {
  return (MIgnorableLLVMIntrinsics.count(Str) > 0);
}

//
// Method: identifyFuncToTrans
//
// Description: This function traverses the module and identifies the
// functions that need to be transformed by SoftBound/CETS
//

void SoftBoundCETSPass::identifyFuncToTrans(Module &module) {

  for (Module::iterator fb_it = module.begin(), fe_it = module.end();
       fb_it != fe_it; ++fb_it) {

    Function *func = dyn_cast<Function>(fb_it);
    assert(func && " Not a function");

    // Check if the function is defined in the module
    if (!func->isDeclaration()) {
      if (isFunctionNotToInstrument(func->getName()))
        continue;

      m_func_softboundcets_transform[func->getName()] = true;
      if (hasPtrArgRetType(func)) {
        m_func_to_transform[func->getName()] = true;
      }
    }
  }
}

//
// Method: introduceGlobalLockFunction()
//
// Description:
//
// This function introduces the function to retrieve the lock for the
// global variables. This function should be introduced only once for
// every function in the entry block of the function.
//

Value *SoftBoundCETSPass::introduceGlobalLockFunction(Instruction *insert_at) {

  SmallVector<Value *, 8> args;
  Value *call_inst = CallInst::Create(GetGlobalLockFn, args, "", insert_at);
  return call_inst;
}

// Method: castToVoidPtr()
//
// Description:
//
// This function introduces a bitcast instruction in the IR when a pointer is
// not of type i8*. This is required as all the runtime handlers take i8*
// pointers.
Value *SoftBoundCETSPass::castToVoidPtr(Value *Ptr, IRBuilder<> &IRB) {
  if (Ptr->getType() == MVoidPtrTy)
    return Ptr;

  if (Constant *C = dyn_cast<Constant>(Ptr))
    return ConstantExpr::getBitCast(C, MVoidPtrTy);

  return IRB.CreateBitCast(Ptr, MVoidPtrTy, Ptr->getName() + ".voidptr");
}

// Helper function castToVoidPtr that creates an IRBuilder from the Instruction.
// TODO[zieris]: Remove when finished rewriting the pass to use IRBuilder
// instead of adding instructions manually.
Value *SoftBoundCETSPass::castToVoidPtr(Value *Op, Instruction *InsertAt) {
  IRBuilder<> IRB(InsertAt);
  return castToVoidPtr(Op, IRB);
}

//
// Method: hasPtrArgRetType()
//
// Description:
//
// This function checks if the function has either pointer arguments
// or returns a pointer value. This function is used to determine
// whether shadow stack loads/stores need to be introduced for
// metadata propagation.
//

bool SoftBoundCETSPass::hasPtrArgRetType(Function *func) {

  const Type *ret_type = func->getReturnType();
  if (isa<PointerType>(ret_type))
    return true;

  for (Function::arg_iterator i = func->arg_begin(), e = func->arg_end();
       i != e; ++i) {

    if (isa<PointerType>(i->getType()))
      return true;
  }
  return false;
}

//
// Method: addStoreBaseBoundFunc
//
// Description:
//
// This function inserts metadata stores into the bitcode whenever a
// pointer is being stored to memory.
//
// Inputs:
//
// pointer_dest: address where the pointer being stored
//
// pointer_base, pointer_bound, pointer_key, pointer_lock: metadata
// associated with the pointer being stored
//
// pointer : pointer being stored to memory
//
// size_of_type: size of the access
//
// insert_at: the insertion point in the bitcode before which the
// metadata store is introduced.
//
void SoftBoundCETSPass::insertPointerMetadataStore(Value *StoreDest,
                                                   Value *Base, Value *Bound,
                                                   Value *Key, Value *Lock,
                                                   Instruction *InsertAt) {
  Value *BaseCast = NULL;
  Value *BoundCast = NULL;

  Value *StoreDestCast = castToVoidPtr(StoreDest, InsertAt);

  if (ClSpatialSafety) {
    BaseCast = castToVoidPtr(Base, InsertAt);
    BoundCast = castToVoidPtr(Bound, InsertAt);
  }

  SmallVector<Value *, 8> Args;

  Args.push_back(StoreDestCast);

  if (ClSpatialSafety) {
    Args.push_back(BaseCast);
    Args.push_back(BoundCast);
  }

  if (ClTemporalSafety) {
    Args.push_back(Key);
    Args.push_back(Lock);
  }
  CallInst::Create(StoreMetadataFn, Args, "", InsertAt);
}

void SoftBoundCETSPass::insertVectorMetadataStore(Value *StoreDest,
                                                  Value *Bases, Value *Bounds,
                                                  Value *Keys, Value *Locks,
                                                  Instruction *InsertAt) {
  SmallVector<Value *, 8> ExtractedBases, ExtractedBounds, ExtractedKeys,
      ExtractedLocks;

  if (ClSpatialSafety) {
    ExtractedBases = extractVectorValues(Bases, InsertAt);
    ExtractedBounds = extractVectorValues(Bounds, InsertAt);
  }
  if (ClTemporalSafety) {
    ExtractedKeys = extractVectorValues(Keys, InsertAt);
    ExtractedLocks = extractVectorValues(Locks, InsertAt);
  }

  const VectorType *VectorTy;
  if (ClSpatialSafety) {
    VectorTy = dyn_cast<VectorType>(Bases->getType());
  } else {
    VectorTy = dyn_cast<VectorType>(Keys->getType());
  }
  ElementCount NumElements = VectorTy->getElementCount();

  Value *PtrOpBitcast = castToVoidPtr(StoreDest, InsertAt);
  SmallVector<Value *, 8> Args;
  for (uint64_t i = 0; i < NumElements.getValue(); i++) {

    Args.clear();
    Constant *Idx =
        ConstantInt::get(Type::getInt32Ty(StoreDest->getContext()), i);
    Args.push_back(PtrOpBitcast);

    if (ClSpatialSafety) {
      Value *PtrBase = ExtractedBases[i];
      Value *PtrBound = ExtractedBounds[i];
      Args.push_back(PtrBase);
      Args.push_back(PtrBound);
    }
    if (ClTemporalSafety) {
      Value *PtrKey = ExtractedKeys[i];
      Value *PtrLock = ExtractedKeys[i];
      Args.push_back(PtrKey);
      Args.push_back(PtrLock);
    }

    Args.push_back(Idx);

    CallInst::Create(StoreVectorMetadataFn, Args, "", InsertAt);
  }
}

//
// The metadata propagation for PHINode occurs in two passes. In the
// first pass, SoftBound/CETS transformation just creates the metadata
// PHINodes and records it in the maps maintained by
// SoftBound/CETS. In the second pass, it populates the incoming
// values of the PHINodes. This two pass approach ensures that every
// incoming value of the original PHINode will have metadata in the
// SoftBound/CETS maps
//

//
// Method: handlePHIPass1()
//
// Description:
//
// This function creates a PHINode for the metadata in the bitcode for
// pointer PHINodes. It is important to note that this function just
// creates the PHINode and does not populate the incoming values of
// the PHINode, which is handled by the handlePHIPass2.
//

void SoftBoundCETSPass::handlePHIPass1(PHINode *PHI) {
  Type *PHITy = PHI->getType();

  // Not a Pointer PHINode, then just return
  if (!isTypeWithPointers(PHITy))
    return;

  unsigned NumIncomingValues = PHI->getNumIncomingValues();

  auto MetadataOrder = getMetadataOrder(PHITy);

  if (ClSpatialSafety) {
    TinyPtrVector<Value *> Bases, Bounds;

    PHINode *BasePHI, *BoundPHI;

    for (auto &MetadataType : MetadataOrder) {
      if (std::get<0>(MetadataType) == 0) {
        BasePHI =
            PHINode::Create(MVoidPtrTy, NumIncomingValues, "phi.base", PHI);

        BoundPHI =
            PHINode::Create(MVoidPtrTy, NumIncomingValues, "phi.bound", PHI);
      } else if (std::get<0>(MetadataType) == 1) {

        auto NumPtrs = std::get<1>(MetadataType);
        VectorType *MetadataVectorTy =
            VectorType::get(MVoidPtrTy, NumPtrs, false);
        BasePHI = PHINode::Create(MetadataVectorTy, NumIncomingValues,
                                  "phi.vector.bases", PHI);
        BoundPHI = PHINode::Create(MetadataVectorTy, NumIncomingValues,
                                   "phi.vector.bounds", PHI);
      } else {
        assert(0 && "Invalid MetadataType returned by getMetadataOrder");
      }
      Bases.push_back(BasePHI);
      Bounds.push_back(BoundPHI);
    }
    associateAggregateBaseBound(PHI, Bases, Bounds);
  }
  if (ClTemporalSafety) {
    TinyPtrVector<Value *> Keys, Locks;

    PHINode *KeyPHI, *LockPHI;
    for (auto &MetadataType : MetadataOrder) {
      if (std::get<0>(MetadataType) == 0) {
        KeyPHI = PHINode::Create(MKeyTy, NumIncomingValues, "phi.key", PHI);
        LockPHI =
            PHINode::Create(MLockPtrTy, NumIncomingValues, "phi.lock", PHI);
      } else if (std::get<0>(MetadataType) == 1) {
        auto NumPtrs = std::get<1>(MetadataType);
        VectorType *LockMetadataVectorTy =
            VectorType::get(MLockPtrTy, NumPtrs, false);
        VectorType *KeyMetadataVectorTy =
            VectorType::get(MKeyTy, NumPtrs, false);

        KeyPHI = PHINode::Create(KeyMetadataVectorTy, NumIncomingValues,
                                 "phi.vector.keys", PHI);
        LockPHI = PHINode::Create(LockMetadataVectorTy, NumIncomingValues,
                                  "phi.vector.locks", PHI);
      } else {
        assert(0 && "Invalid MetadataType returned by getMetadataOrder");
      }
      Keys.push_back(KeyPHI);
      Locks.push_back(LockPHI);
    }
    associateAggregateKeyLock(PHI, Keys, Locks);
  }
}

//
// Method: handlePHIPass2()
//
// Description: This pass fills the incoming values for the metadata
// PHINodes inserted in the first pass. There are four cases that
// needs to be handled for each incoming value.  First, if the
// incoming value is a ConstantPointerNull, then base, bound, key,
// lock will be default values.  Second, the incoming value can be an
// undef which results in default metadata values.  Third, Global
// variables need to get the same base and bound for each
// occurence. So we maintain a map which maps the base and boundfor
// each global variable in the incoming value.  Fourth, by default it
// retrieves the metadata from the SoftBound/CETS maps.

// Check if we need separate global variable and constant expression
// cases.

void SoftBoundCETSPass::handlePHIPass2(PHINode *PHI) {
  Type *PHITy = PHI->getType();

  // Not a Pointer PHINode, then just return
  if (!isTypeWithPointers(PHITy))
    return;

  unsigned NumIncomingValues = PHI->getNumIncomingValues();
  // each PHI can have multiple metadata for each pointer/ptrvector contained in
  // the type
  ArrayRef<Value *> PHIBases;
  ArrayRef<Value *> PHIBounds;
  ArrayRef<Value *> PHIKeys;
  ArrayRef<Value *> PHILocks;
  size_t BasesSize;
  size_t KeysSize;

  if (ClSpatialSafety) {
    PHIBases = getAssociatedBases(PHI);
    PHIBounds = getAssociatedBounds(PHI);
    BasesSize = PHIBases.size();
  }
  if (ClTemporalSafety) {
    PHIKeys = getAssociatedKeys(PHI);
    PHILocks = getAssociatedLocks(PHI);
    KeysSize = PHIKeys.size();
  }

  for (unsigned M = 0; M < NumIncomingValues; M++) {
    auto *IncomingBB = PHI->getIncomingBlock(M);
    auto *IncomingVal = PHI->getIncomingValue(M);

    // each incoming value has also its metadata
    if (ClSpatialSafety) {
      auto IncomingBases = getAssociatedBases(IncomingVal);
      auto IncomingBasesSize = IncomingBases.size();
      assert(
          (BasesSize == IncomingBasesSize) &&
          "PHIPass2: Bases of PHI do not have same length as incoming Bases");
      auto IncomingBounds = getAssociatedBounds(IncomingVal);

      // iterate over bases
      for (size_t J = 0; J < BasesSize; J++) {
        auto *PHIBase = dyn_cast<PHINode>(PHIBases[J]);
        auto *PHIBound = dyn_cast<PHINode>(PHIBounds[J]);
        PHIBase->addIncoming(IncomingBases[J], IncomingBB);
        PHIBound->addIncoming(IncomingBounds[J], IncomingBB);
      }
    }
    if (ClTemporalSafety) {
      auto IncomingKeys = getAssociatedKeys(IncomingVal);
      auto IncomingKeysSize = IncomingKeys.size();
      assert(
          (KeysSize == IncomingKeysSize) &&
          "PHIPass2: Bases of PHI do not have same length as incoming Bases");
      auto IncomingLocks = getAssociatedLocks(IncomingVal);

      // iterate over keys
      for (size_t J = 0; J < KeysSize; J++) {
        auto *PHIKey = dyn_cast<PHINode>(PHIKeys[J]);
        auto *PHILock = dyn_cast<PHINode>(PHILocks[J]);
        PHIKey->addIncoming(IncomingKeys[J], IncomingBB);
        PHILock->addIncoming(IncomingLocks[J], IncomingBB);
      }
    }
  } // Iterating over incoming values ends
}

//
// Method: propagateMetadata
//
// Descripton;
//
// This function propagates the metadata from the source to the
// destination in the map for pointer arithmetic operations~(gep) and
// bitcasts. This is the place where we need to shrink bounds.
//

void SoftBoundCETSPass::propagateMetadata(Value *Src, Instruction *Dest) {
  // Need to just propagate the base and bound here if I am not
  // shrinking bounds
  if (checkMetadataPresent(Dest)) {
    return;
  }

  if (ClSpatialSafety) {
    auto Bases = TinyPtrVector<Value *>(getAssociatedBases(Src));
    auto Bounds = TinyPtrVector<Value *>(getAssociatedBounds(Src));
    associateAggregateBaseBound(Dest, Bases, Bounds);
  }
  if (ClTemporalSafety) {
    auto Keys = TinyPtrVector<Value *>(getAssociatedKeys(Src));
    auto Locks = TinyPtrVector<Value *>(getAssociatedLocks(Src));
    associateAggregateKeyLock(Dest, Keys, Locks);
  }
  return;
}

//
// Method: handleBitCast
//
// Description: Propagate metadata from source to destination with
// pointer bitcast operations.

void SoftBoundCETSPass::handleBitCast(BitCastInst *BC) {
  Value *PtrOp = BC->getOperand(0);
  propagateMetadata(PtrOp, BC);
}

//
// Method: introduceShadowStackAllocation
//
// Description: For every function call that has a pointer argument or
// a return value, shadow stack is used to propagate metadata. This
// function inserts the shadow stack allocation C-handler that
// reserves space in the shadow stack by reserving the requiste amount
// of space based on the input passed to it(number of pointer
// arguments/return).

void SoftBoundCETSPass::introduceShadowStackAllocation(CallBase *CallInst,
                                                       int NumPtrs) {
  Value *NumTotalPtrArgs = ConstantInt::get(
      Type::getInt64Ty(CallInst->getType()->getContext()), NumPtrs, false);
  TinyPtrVector<Value *> Args;
  Args.push_back(NumTotalPtrArgs);
  CallInst::Create(AllocateShadowStackFn, Args, "", CallInst);
}

//
// Method: introduceShadowStackStores
//
// Description: This function inserts a call to the shadow stack store
// C-handler that stores the metadata, before the function call in the
// bitcode for pointer arguments.

size_t SoftBoundCETSPass::introduceShadowStackStores(Value *Val,
                                                     Instruction *InsertAt,
                                                     int ArgNo) {
  size_t NumPtrs = countPointersInType(Val->getType());
  if (NumPtrs == 0)
    return 0;

  SmallVector<Value *, 8> Args, UnpackedBases, UnpackedBounds, UnpackedKeys,
      UnpackedLocks;
  unsigned MetadataSize = 0;
  IRBuilder<> IRB(InsertAt);

  /** (ds)
   * Push metadata of each contained pointer on the shadow stack linearly.
   */
  if (ClSpatialSafety) {
    auto AssociatedBases = getAssociatedBases(Val);
    auto AssociatedBounds = getAssociatedBounds(Val);
    UnpackedBases = unpackMetadataArray(AssociatedBases, InsertAt);
    UnpackedBounds = unpackMetadataArray(AssociatedBounds, InsertAt);
    MetadataSize = UnpackedBases.size();
  }
  if (ClTemporalSafety) {
    auto AssociatedKeys = getAssociatedKeys(Val);
    auto AssociatedLocks = getAssociatedLocks(Val);
    UnpackedKeys = unpackMetadataArray(AssociatedKeys, InsertAt);
    UnpackedLocks = unpackMetadataArray(AssociatedLocks, InsertAt);
    MetadataSize = UnpackedKeys.size();
  }

  for (unsigned Idx = 0; Idx < MetadataSize; ++Idx) {
    Args.clear();
    if (ClSpatialSafety) {
      Value *BaseCast = castToVoidPtr(UnpackedBases[Idx], InsertAt);
      Args.push_back(BaseCast);
      Value *BoundCast = castToVoidPtr(UnpackedBounds[Idx], InsertAt);
      Args.push_back(BoundCast);
    }
    if (ClTemporalSafety) {
      Args.push_back(UnpackedKeys[Idx]);
      Args.push_back(UnpackedLocks[Idx]);
    }
    Args.push_back(ConstantInt::get(MArgNoTy, ArgNo + Idx, false));
    IRB.CreateCall(StoreMetadataShadowStackFn, Args);
  }

  return NumPtrs;
}

//
// Method: introduceShadowStackDeallocation
//
// Description: This function inserts a call to the C-handler that
// deallocates the shadow stack space on function exit.

void SoftBoundCETSPass::introduceShadowStackDeallocation(
    CallBase *CallInst, Instruction *InsertAt) {
  TinyPtrVector<Value *> Args;
  CallInst::Create(DeallocateShadowStackFn, Args, "", InsertAt);
}

//
// Method: getNumPointerArgs
//
// Description: Returns the number of pointer arguments and return.
//
size_t SoftBoundCETSPass::getNumPointerArgs(const CallBase *CB) {
  size_t NumPointerArgs = 0;

  for (const Use &Arg : CB->args())
    NumPointerArgs += countPointersInType(Arg->getType());

  return NumPointerArgs;
}

//
// Method: introduceShadowStackLoads
//
// Description: This function introduces calls to the C-handlers that
// performs the loads from the shadow stack to retrieve the metadata.
// This function also associates the loaded metadata with the pointer
// arguments in the SoftBound/CETS maps.

size_t SoftBoundCETSPass::introduceShadowStackLoads(Value *Val,
                                                    Instruction *InsertAt,
                                                    int ArgNo) {
  size_t NumPtrs = countPointersInType(Val->getType());
  if (!NumPtrs)
    return 0;

  IRBuilder<> IRB(InsertAt);

  Type *ValTy = Val->getType();

  TinyPtrVector<Value *> Bases;
  TinyPtrVector<Value *> Bounds;
  TinyPtrVector<Value *> Keys;
  TinyPtrVector<Value *> Locks;

  unsigned KeyIdx = 0;
  unsigned LockIdx = 1;
  if (ClSpatialSafety) {
    KeyIdx = 2;
    LockIdx = 3;
  }

  if (ClSimpleMetadataMode) {

    SmallVector<Value *, 8> Args;
    for (unsigned PtrIdx = 0; PtrIdx < NumPtrs; ++PtrIdx) {
      Args.clear();

      Args.push_back(ConstantInt::get(MArgNoTy, ArgNo + PtrIdx, false));
      if (ClSpatialSafety) {
        Value *Base = IRB.CreateCall(LoadBaseShadowStackFn, Args, "");
        Bases.push_back(Base);

        Value *Bound = IRB.CreateCall(LoadBoundShadowStackFn, Args, "");
        Bounds.push_back(Bound);
      }

      if (ClTemporalSafety) {
        Value *Key = IRB.CreateCall(LoadKeyShadowStackFn, Args, "");
        Keys.push_back(Key);
        Value *Lock = IRB.CreateCall(LoadLockShadowStackFn, Args, "");
        Locks.push_back(Lock);
      }
    }

  } else {

    for (unsigned PtrIdx = 0; PtrIdx < NumPtrs; ++PtrIdx) {
      auto *MetadataPtr =
          IRB.CreateCall(LoadMetadataPtrShadowStackFn,
                         {ConstantInt::get(MArgNoTy, ArgNo + PtrIdx, false)},
                         "shadow_stack_metadata_ptr");

      if (ClSpatialSafety) {
        auto *BasePtr = IRB.CreateStructGEP(MetadataPtr, 0, "baseptr");
        auto *Base = IRB.CreateLoad(BasePtr, "base");
        auto *BoundPtr = IRB.CreateStructGEP(MetadataPtr, 1, "boundptr");
        auto *Bound = IRB.CreateLoad(BoundPtr, "bound");
        Bases.push_back(Base);
        Bounds.push_back(Bound);
      }
      if (ClTemporalSafety) {
        auto *KeyPtr = IRB.CreateStructGEP(MetadataPtr, KeyIdx, "keyptr");
        auto *Key = IRB.CreateLoad(KeyPtr, "key");
        auto *LockPtr = IRB.CreateStructGEP(MetadataPtr, LockIdx, "lockptr");
        auto *Lock = IRB.CreateLoad(LockPtr, "lock");
        Keys.push_back(Key);
        Locks.push_back(Lock);
      }
    }
  }

  if (ClSpatialSafety) {
    auto PackedBases = packMetadataArray(Bases, ValTy, InsertAt);
    auto PackedBounds = packMetadataArray(Bounds, ValTy, InsertAt);
    associateAggregateBaseBound(Val, PackedBases, PackedBounds);
  }
  if (ClTemporalSafety) {
    auto PackedKeys = packMetadataArray(Keys, ValTy, InsertAt);
    auto PackedLocks = packMetadataArray(Locks, ValTy, InsertAt);
    associateAggregateKeyLock(Val, PackedKeys, PackedLocks);
  }

  return NumPtrs;
}
//
// Method: dissociateKeyLock
//
// Description: This function removes the key lock metadata associated
// with the pointer operand in the SoftBound/CETS maps.
void SoftBoundCETSPass::dissociateKeyLock(Value *pointer_operand) {
  if (MValueKeyMap.count(pointer_operand)) {
    MValueKeyMap.erase(pointer_operand);
  }
  if (MValueLockMap.count(pointer_operand)) {
    MValueLockMap.erase(pointer_operand);
  }
  assert((MValueKeyMap.count(pointer_operand) == 0) &&
         "dissociating key failed");
  assert((MValueLockMap.count(pointer_operand) == 0) &&
         "dissociating lock failed");
}
//
// Method: dissociateBaseBound
//
// Description: This function removes the base/bound metadata
// associated with the pointer operand in the SoftBound/CETS maps.

void SoftBoundCETSPass::dissociateBaseBound(Value *pointer_operand) {
  if (MValueBaseMap.count(pointer_operand)) {
    MValueBaseMap.erase(pointer_operand);
  }
  if (MValueBoundMap.count(pointer_operand)) {
    MValueBoundMap.erase(pointer_operand);
  }
  assert((MValueBaseMap.count(pointer_operand) == 0) &&
         "dissociating base failed\n");
  assert((MValueBoundMap.count(pointer_operand) == 0) &&
         "dissociating bound failed");
}
void SoftBoundCETSPass::associateMetadata(
    Value *Val, const SoftBoundCETSMetadata &Metadata) {
  if (ClSpatialSafety) {
    associateBaseBound(Val, Metadata.Base, Metadata.Bound);
  }
  if (ClTemporalSafety) {
    associateKeyLock(Val, Metadata.Key, Metadata.Lock);
  }
}

void SoftBoundCETSPass::associateMetadata(Value *Val, Value *Base, Value *Bound,
                                          Value *Key, Value *Lock) {
  if (ClSpatialSafety) {
    associateBaseBound(Val, Base, Bound);
  }
  if (ClTemporalSafety) {
    associateKeyLock(Val, Key, Lock);
  }
}

void SoftBoundCETSPass::associateAggregateMetadata(
    Value *Val, TinyPtrVector<Value *> &Bases, TinyPtrVector<Value *> &Bounds,
    TinyPtrVector<Value *> &Keys, TinyPtrVector<Value *> &Locks) {
  if (ClSpatialSafety) {
    associateAggregateBaseBound(Val, Bases, Bounds);
  }
  if (ClTemporalSafety) {
    associateAggregateKeyLock(Val, Keys, Locks);
  }
}

Value *
SoftBoundCETSPass::createMetadataVector(ArrayRef<Value *> SingleMetadataVals,
                                        Instruction *InsertAt) {

  uint64_t NumPtrs = SingleMetadataVals.size();
  FixedVectorType *MetadataVectorTy =
      FixedVectorType::get(SingleMetadataVals.front()->getType(), NumPtrs);
  Value *MetadataVector = UndefValue::get(MetadataVectorTy);
  for (uint64_t J = 0; J < NumPtrs; J++) {
    Constant *Idx =
        ConstantInt::get(Type::getInt32Ty(InsertAt->getContext()), J);
    MetadataVector = InsertElementInst::Create(
        MetadataVector, SingleMetadataVals[J], Idx, "", InsertAt);
  }
  return MetadataVector;
}

SmallVector<Value *, 8>
SoftBoundCETSPass::extractVectorBases(Value *Val, Instruction *InsertAt) {
  auto *BasesVector = getAssociatedBase(Val);
  return extractVectorValues(BasesVector, InsertAt);
}

SmallVector<Value *, 8>
SoftBoundCETSPass::extractVectorBounds(Value *Val, Instruction *InsertAt) {
  auto *BoundsVector = getAssociatedBound(Val);
  return extractVectorValues(BoundsVector, InsertAt);
}

SmallVector<Value *, 8>
SoftBoundCETSPass::extractVectorKeys(Value *Val, Instruction *InsertAt) {
  auto *KeysVector = getAssociatedKey(Val);
  return extractVectorValues(KeysVector, InsertAt);
}

SmallVector<Value *, 8>
SoftBoundCETSPass::extractVectorLocks(Value *Val, Instruction *InsertAt) {
  auto *LocksVector = getAssociatedLock(Val);
  return extractVectorValues(LocksVector, InsertAt);
}

SmallVector<Value *, 8>
SoftBoundCETSPass::extractVectorValues(Value *MetadataVector,
                                       Instruction *InsertAt) {
  const VectorType *VectorTy = dyn_cast<VectorType>(MetadataVector->getType());
  assert(VectorTy && "MetadataVector Value is not a VectorType");
  ElementCount NumElements = VectorTy->getElementCount();
  SmallVector<Value *, 8> Metadata;

  for (uint64_t I = 0; I < NumElements.getValue(); I++) {
    Constant *Idx =
        ConstantInt::get(Type::getInt32Ty(InsertAt->getContext()), I);
    Value *Metadatum =
        ExtractElementInst::Create(MetadataVector, Idx, "", InsertAt);
    Metadata.push_back(Metadatum);
  }
  return Metadata;
}

//
// Method: associateKeyLock
//
// Description: This function associates the key lock with the pointer
// operand in the SoftBound/CETS maps.

inline void SoftBoundCETSPass::associateKeyLock(Value *Val, Value *Key,
                                                Value *Lock) {
  if (MValueKeyMap.count(Val)) {
    dissociateKeyLock(Val);
  }

  assert(isValidMetadata(Key, MetadataType::Key) && "Invalid key metadata");
  assert(isValidMetadata(Lock, MetadataType::Lock) && "Invalid lock metadata");

  MValueKeyMap[Val] = {Key};
  MValueLockMap[Val] = {Lock};
}

inline void
SoftBoundCETSPass::associateAggregateBase(Value *Val,
                                          TinyPtrVector<Value *> &Bases) {
  auto NumMetadata = countMetadata(Val->getType());
  assert(NumMetadata == Bases.size() &&
         "Bases size is not equal to number of metadata in type");

  for (auto &Base : Bases) {
    assert(isValidMetadata(Base, MetadataType::Base) &&
           "Invalid base metadata");
  }
  MValueBaseMap[Val] = Bases;
}

inline void
SoftBoundCETSPass::associateAggregateBound(Value *Val,
                                           TinyPtrVector<Value *> &Bounds) {
  auto NumMetadata = countMetadata(Val->getType());
  assert(NumMetadata == Bounds.size() &&
         "Bounds size is not equal to number of metadata in type");

  for (auto &Bound : Bounds) {
    assert(isValidMetadata(Bound, MetadataType::Bound) &&
           "Invalid bound metadata");
  }
  MValueBoundMap[Val] = Bounds;
}

inline void SoftBoundCETSPass::associateAggregateBaseBound(
    Value *Val, TinyPtrVector<Value *> &Bases, TinyPtrVector<Value *> &Bounds) {
  if (MValueBaseMap.count(Val)) {
    dissociateBaseBound(Val);
  }
  associateAggregateBase(Val, Bases);
  associateAggregateBound(Val, Bounds);
}

inline void SoftBoundCETSPass::associateAggregateKeyLock(
    Value *Val, TinyPtrVector<Value *> &Keys, TinyPtrVector<Value *> &Locks) {
  if (MValueBaseMap.count(Val)) {
    dissociateKeyLock(Val);
  }

  auto MetadataSize = countMetadata(Val->getType());
  assert(MetadataSize == Keys.size() &&
         "Keys size is not equal to metadata size of type");
  assert(MetadataSize == Locks.size() &&
         "Locks size is not equal to metadata size of type");

  for (auto &Key : Keys) {
    assert(isValidMetadata(Key, MetadataType::Key) && "Invalid key metadata");
  }
  for (auto &Lock : Locks) {
    assert(isValidMetadata(Lock, MetadataType::Lock) &&
           "Invalid lock metadata");
  }

  MValueKeyMap[Val] = Keys;
  MValueLockMap[Val] = Locks;
}

inline bool SoftBoundCETSPass::isValidMetadata(Value *Metadatum,
                                               MetadataType MetadataTy) {
  auto *ValTy = Metadatum->getType();
  switch (MetadataTy) {
  case Base:
  case Bound: {
    if (ValTy == MVoidPtrTy)
      return true;
    auto *VectorTy = dyn_cast<FixedVectorType>(ValTy);
    if (VectorTy && (VectorTy->getElementType() == MVoidPtrTy))
      return true;
    return false;

    break;
  }
  case Key: {
    if (ValTy == MKeyTy)
      return true;
    auto *VectorTy = dyn_cast<FixedVectorType>(ValTy);
    if (VectorTy && (VectorTy->getElementType() == MKeyTy))
      return true;
    return false;

    break;
  }
  case Lock: {
    if (ValTy == MLockPtrTy)
      return true;
    auto *VectorTy = dyn_cast<FixedVectorType>(ValTy);
    if (VectorTy && (VectorTy->getElementType() == MLockPtrTy))
      return true;
    return false;

    break;
  }
  }

  return false;
}

//
// Method: associateBaseBound
//
// Description: This function associates the base bound with the
// pointer operand in the SoftBound/CETS maps.

inline void SoftBoundCETSPass::associateBaseBound(Value *Val, Value *Base,
                                                  Value *Bound) {
  if (MValueBaseMap.count(Val)) {
    dissociateBaseBound(Val);
  }

  assert(isValidMetadata(Base, MetadataType::Base) && "Invalid base metadata");
  assert(isValidMetadata(Bound, MetadataType::Bound) &&
         "Invalid bound metadata");

  MValueBaseMap[Val] = {Base};
  MValueBoundMap[Val] = {Bound};
}
//
// Method: handleSelect
//
// This function propagates the metadata with Select IR instruction.
void SoftBoundCETSPass::handleSelect(SelectInst *Select) {
  auto *SelectTy = Select->getType();
  if (!isTypeWithPointers(SelectTy))
    return;

  Value *Condition = Select->getOperand(0);
  ArrayRef<Value *> OpBases[2];
  ArrayRef<Value *> OpBounds[2];
  ArrayRef<Value *> OpKeys[2];
  ArrayRef<Value *> OpLocks[2];

  for (unsigned M = 0; M < 2; M++) {
    Value *Op = Select->getOperand(M + 1);

    if (ClSpatialSafety) {
      OpBases[M] = getAssociatedBases(Op);
      OpBounds[M] = getAssociatedBounds(Op);
    }

    if (ClTemporalSafety) {
      OpKeys[M] = getAssociatedKeys(Op);
      OpLocks[M] = getAssociatedLocks(Op);
    }
  }

  // two possibilities:
  // 1) Condition is an i1; then we just create a select for each metadata the
  // type contains
  // 2) Condition is a vector of i1; this means both arguments are
  // also vectors
  //    then we need to unpack each metadata vector of each argument, create
  //    selects for the contained bases/bounds... and repack the metadata into a
  //    vector for the Select result

  if (Condition->getType()->isIntegerTy(1)) {

    if (ClSpatialSafety) {
      TinyPtrVector<Value *> Bases, Bounds;

      for (size_t M = 0; M < OpBases[0].size(); M++) {
        SelectInst *Base, *Bound;
        Base = SelectInst::Create(Condition, OpBases[0][M], OpBases[1][M],
                                  "select.base", Select);

        Bound = SelectInst::Create(Condition, OpBounds[0][M], OpBounds[1][M],
                                   "select.bound", Select);

        Bases.push_back(Base);
        Bounds.push_back(Bound);
      }

      associateAggregateBaseBound(Select, Bases, Bounds);
    }

    if (ClTemporalSafety) {
      TinyPtrVector<Value *> Keys, Locks;

      for (size_t M = 0; M < OpKeys[0].size(); M++) {
        SelectInst *Key, *Lock;
        Key = SelectInst::Create(Condition, OpKeys[0][M], OpKeys[1][M],
                                 "select.key", Select);

        Lock = SelectInst::Create(Condition, OpLocks[0][M], OpLocks[1][M],
                                  "select.lock", Select);

        Keys.push_back(Key);
        Locks.push_back(Lock);
      }

      associateAggregateKeyLock(Select, Keys, Locks);
    }
  } else { // Condition is a vector of i1
           // TODO: merge this with previous if branch
    assert(Condition->getType()->isVectorTy() &&
           "select condition not a vector");

    if (ClSpatialSafety) {
      auto *Base = SelectInst::Create(Condition, OpBases[0][0], OpBases[1][0],
                                      "select.base", Select);
      auto *Bound = SelectInst::Create(Condition, OpBounds[0][0],
                                       OpBounds[1][0], "select.bound", Select);
      associateBaseBound(Select, Base, Bound);
    }

    if (ClTemporalSafety) {

      auto *Key = SelectInst::Create(Condition, OpKeys[0][0], OpKeys[1][0],
                                     "select.key", Select);
      auto *Lock = SelectInst::Create(Condition, OpLocks[0][0], OpLocks[1][0],
                                      "select.lock", Select);
      associateKeyLock(Select, Key, Lock);
    }
  }
}

bool SoftBoundCETSPass::checkMetadataPresent(Value *Op) {
  bool MetadataPresent = false;
  if (ClSpatialSafety) {
    MetadataPresent = checkBaseBoundMetadataPresent(Op);
  } else {
    MetadataPresent = true;
  }
  if (ClTemporalSafety) {
    MetadataPresent = (MetadataPresent && checkKeyLockMetadataPresent(Op));
  }
  return MetadataPresent;
}

//
// Method: checkBaseBoundMetadataPresent()
//
// Description:
// Checks if the metadata is present in the SoftBound/CETS maps.

bool SoftBoundCETSPass::checkBaseBoundMetadataPresent(Value *Op) {
  return MValueBaseMap.count(Op) && MValueBoundMap.count(Op);
}

//
// Method: checkKeyLockMetadataPresent()
//
// Description:
// Checks if the metadata is present in the SoftBound/CETS maps.

bool SoftBoundCETSPass::checkKeyLockMetadataPresent(Value *Op) {
  return MValueKeyMap.count(Op) && MValueLockMap.count(Op);
}

//
// Method: handleReturnInst
//
// Description:
// This function inserts C-handler calls to store
// metadata for return values in the shadow stack.

void SoftBoundCETSPass::handleReturnInst(ReturnInst *Ret) {
  Value *RetVal = Ret->getReturnValue();
  if (RetVal == NULL) {
    return;
  }
  Type *RetTy = RetVal->getType();
  if (!isTypeWithPointers(RetTy))
    return;

  introduceShadowStackStores(RetVal, Ret, 0);
}

//
// Method: getConstantExprBaseBound
//
// Description: This function uniform handles all global constant
// expression and obtains the base and bound for these expressions
// without introducing any extra IR modifications.
//
// WARNING: This method only handles constants with a single pointer correctly.
// For constants containing multiple pointers use getConstantExprBaseBoundArray.

void SoftBoundCETSPass::getConstantExprBaseBound(Constant *given_constant,
                                                 Value *&tmp_base,
                                                 Value *&tmp_bound) {
  TinyPtrVector<Value *> bases, bounds;
  getConstantExprBaseBoundArray(given_constant, bases, bounds);
  assert(bases.size() == 1 && bounds.size() == 1 &&
         "getConstantExprBaseBound called on aggregate");
  tmp_base = bases[0];
  tmp_bound = bounds[0];
}

//
// Methods: getAssociatedBase(Array), getAssociatedBound(Array),
// getAssociatedKey(Array), getAssociatedLock(Array)
//
// Description: Retrieves the metadata from SoftBound/CETS maps
//

/** (ds)
 * The methods with an -Array suffix return all associated metadata
 * entries while those without the suffix only return a single value.
 * Thus, the -Array methods must be used if the value potentially
 * contains multiple pointers (i.e. is an aggregate value).
 * The non-Array methods exist mostly for compatibility reasons,
 * since aggregates are not yet supported everywhere.
 * Further, the non-Array methods check whether the given value is a
 * constant and call getConstantExprBaseBound in this case.
 * When using the -Array methods, this must be checked manually by
 * the caller.
 */

ArrayRef<Value *> SoftBoundCETSPass::getAssociatedBases(Value *Val) {
  if (!MValueBaseMap.count(Val)) {
    if (auto *Const = dyn_cast<Constant>(Val)) {
      auto Bases = createConstantBases<Value>(Const);
      associateAggregateBase(Val, Bases);
    } else if (ClAssociateMissingMetadata) {
      auto DummyMetadata =
          createDummyMetadata<Value>(Val->getType(), MVoidNullPtr);
      associateAggregateBase(Val, DummyMetadata);
    } else {
      LLVM_DEBUG(errs() << "Missing base(s) for Value: " << *Val << '\n');
      assert(0 && "No associated base(s)");
    }
  }
  return MValueBaseMap[Val];
}

// WARNING: This method only handles constants with a single pointer correctly.
// For constants containing multiple pointers use getAssociatedBaseArray.
Value *SoftBoundCETSPass::getAssociatedBase(Value *pointer_operand) {
  ArrayRef<Value *> base_array = getAssociatedBases(pointer_operand);
  assert(base_array.size() == 1 && "getAssociatedBase called on aggregate");
  Value *pointer_base = base_array[0];

  return pointer_base;
}

ArrayRef<Value *> SoftBoundCETSPass::getAssociatedBounds(Value *Val) {
  if (!MValueBoundMap.count(Val)) {
    if (auto *Const = dyn_cast<Constant>(Val)) {
      auto Bounds = createConstantBounds<Value>(Const);
      associateAggregateBound(Val, Bounds);
    } else if (ClAssociateMissingMetadata) {
      Constant *Metadatum;
      if (ClAssociateOmnivalidMetadataWhenMissing) {
        Metadatum = MInfiniteBoundPtr;
      } else {
        Metadatum = MVoidNullPtr;
      }
      auto DummyMetadata =
          createDummyMetadata<Value>(Val->getType(), Metadatum);
      MValueBoundMap[Val] = DummyMetadata;
    } else {
      LLVM_DEBUG(errs() << "Missing bound(s) for value: " << *Val << '\n');
      assert(0 && "No associated bound(s)");
    }
  }
  return MValueBoundMap[Val];
}

// WARNING: This method only handles constants with a single pointer correctly.
// For constants containing multiple pointers use getAssociatedBoundArray.
Value *SoftBoundCETSPass::getAssociatedBound(Value *pointer_operand) {
  ArrayRef<Value *> bound_array = getAssociatedBounds(pointer_operand);
  assert(bound_array.size() == 1 && "getAssociatedBound called on aggregate");
  Value *pointer_bound = bound_array[0];

  return pointer_bound;
}

ArrayRef<Value *> SoftBoundCETSPass::getAssociatedKeys(Value *Val) {
  if (!MValueKeyMap.count(Val)) {
    if (isa<Constant>(Val)) {
      auto DummyMetadata =
          createDummyMetadata<Value>(Val->getType(), MConstantIntOne);
      MValueKeyMap[Val] = DummyMetadata;
    } else if (ClAssociateMissingMetadata) {
      Constant *Metadatum;
      if (ClAssociateOmnivalidMetadataWhenMissing)
        Metadatum = MConstantIntOne;
      else
        Metadatum = MConstantIntZero;

      auto DummyMetadata =
          createDummyMetadata<Value>(Val->getType(), Metadatum);
      MValueKeyMap[Val] = DummyMetadata;
    } else {
      LLVM_DEBUG(errs() << "Missing key(s) for value: " << *Val << '\n');
      assert(0 && "No associated key(s)");
    }
  }
  return MValueKeyMap[Val];
}

// WARNING: This method only handles constants with a single pointer correctly.
// For constants containing multiple pointers use getAssociatedKeyArray.
Value *SoftBoundCETSPass::getAssociatedKey(Value *pointer_operand) {
  if (!ClTemporalSafety) {
    return NULL;
  }

  ArrayRef<Value *> key_array = getAssociatedKeys(pointer_operand);
  assert(key_array.size() == 1 && "getAssociatedKey called on aggregate");
  Value *pointer_key = key_array[0];

  return pointer_key;
}

ArrayRef<Value *> SoftBoundCETSPass::getAssociatedLocks(Value *Val) {
  if (!MValueLockMap.count(Val)) {
    if (isa<Constant>(Val)) {
      auto DummyMetadata =
          createDummyMetadata<Value>(Val->getType(), MGlobalLockOne);
      MValueLockMap[Val] = DummyMetadata;
    } else if (ClAssociateMissingMetadata) {
      auto DummyMetadata = createDummyLocks(Val->getType());
      MValueLockMap[Val] = DummyMetadata;
    } else {
      LLVM_DEBUG(errs() << "Missing lock(s) for value: " << *Val << '\n');
      assert(0 && "No associated lock(s)");
    }
  }
  return MValueLockMap[Val];
}

// WARNING: This method only handles constants with a single pointer correctly.
// For constants containing multiple pointers use getAssociatedLockArray.
Value *SoftBoundCETSPass::getAssociatedLock(Value *pointer_operand) {
  if (!ClTemporalSafety) {
    return NULL;
  }

  ArrayRef<Value *> lock_array = getAssociatedLocks(pointer_operand);
  assert(lock_array.size() == 1 && "getAssociatedLock called on aggregate");
  Value *pointer_lock = lock_array[0];

  return pointer_lock;
}
//
// Method: transformFunctionName
//
// Description:
//
// This function returns the transformed name for the function. This
// function appends softboundcets_ to the input string.

std::string SoftBoundCETSPass::transformFunctionName(const std::string &str) {
  // If the function name starts with this prefix, don't just
  // concatenate, but instead transform the string
  return "softboundcets_" + str;
}

void SoftBoundCETSPass::addMemcopyMemsetCheck(CallBase *CB, Function *F) {
  if (DISABLE_MEMCOPYCHECK)
    return;

  SmallVector<Value *, 8> Args;

  if (F->getName().find("llvm.memcpy") == 0 ||
      F->getName().find("llvm.memmove") == 0) {

    Value *Dest = CB->getArgOperand(0);
    Value *Src = CB->getArgOperand(1);
    Value *Size = CB->getArgOperand(2);

    Args.push_back(Dest);
    Args.push_back(Src);

    Value *SizeCast = Size;
    if (Size->getType() != MSizetTy) {
      SizeCast = CastInst::CreateZExtOrBitCast(Size, MSizetTy, "size.cast", CB);
    }

    Args.push_back(SizeCast);
    if (ClSpatialSafety) {
      Value *DestBase = getAssociatedBase(Dest);
      Value *DestBound = getAssociatedBound(Dest);

      Value *SrcBase = getAssociatedBase(Src);
      Value *SrcBound = getAssociatedBound(Src);

      Args.push_back(DestBase);
      Args.push_back(DestBound);

      Args.push_back(SrcBase);
      Args.push_back(SrcBound);
    }

    if (ClTemporalSafety) {
      Value *DestKey = getAssociatedKey(Dest);
      Value *DestLock = getAssociatedLock(Dest);

      Value *SrcKey = getAssociatedKey(Src);
      Value *SrcLock = getAssociatedLock(Src);

      Args.push_back(DestKey);
      Args.push_back(DestLock);
      Args.push_back(SrcKey);
      Args.push_back(SrcLock);
    }

    CallInst::Create(MemcpyDereferenceCheckFn, Args, "", CB);
    return;
  }

  if (F->getName().find("llvm.memset") == 0) {

    Args.clear();
    Value *Dest = CB->getArgOperand(0);
    // arg 1 is the byte to be written to memory
    Value *Size = CB->getArgOperand(2);

    Value *SizeCast = Size;
    if (Size->getType() != MSizetTy) {
      SizeCast = CastInst::CreateZExtOrBitCast(Size, MSizetTy, "size.cast", CB);
    }
    auto *DestCast = castToVoidPtr(Dest, CB);
    Args.push_back(DestCast);
    Args.push_back(SizeCast);

    if (ClSpatialSafety) {
      Value *DestBase = getAssociatedBase(Dest);
      Value *DestBound = getAssociatedBound(Dest);
      Args.push_back(DestBase);
      Args.push_back(DestBound);
    }

    if (ClTemporalSafety) {
      Value *DestKey = getAssociatedKey(Dest);
      Value *DestLock = getAssociatedLock(Dest);

      Args.push_back(DestKey);
      Args.push_back(DestLock);
    }
    CallInst::Create(MemsetDereferenceCheckFn, Args, "", CB);

    return;
  }
}

//
// Method: getSizeOfType
//
// Description: This function returns the size of the memory access
// based on the type of the pointer which is being dereferenced.  This
// function is used to pass the size of the access in many checks to
// perform byte granularity checking.
//
// Comments: May we should use TargetData instead of m_is_64_bit
// according Criswell's comments.

// // Method: getSizeOfType // // Description: This function returns how many
// bytes Ty occupies in memory. This // function is used to pass the size of the
// access in many checks to perform // byte granularity checking.
ConstantInt *SoftBoundCETSPass::getSizeOfType(Type *Ty) {
  if (!Ty->isSized())
    return ConstantInt::get(Type::getInt64Ty(*C), 0);
  return ConstantInt::get(Type::getInt64Ty(*C), DL->getTypeStoreSize(Ty));
}

// Method: isStructOperand
//
//
// Description: This function elides the checks for the structure
// accesses. This is safe when there are no casts in the program.
//
bool SoftBoundCETSPass::isStructOperand(Value *pointer_operand) {
  GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(pointer_operand);
  return GEP && isa<StructType>(GEP->getSourceElementType());
}

//
// This Code is from SAFECode Project.
// Function: createFaultBlock()
//
// Description:
//  Create a basic block which will cause the program to terminate.
//
// Inputs:
// F - A pointer to a function to which a faulting basic block
//  will be added.
//
static BasicBlock *createFaultBlock(Function *F) {
  //
  // Create the basic block.
  //
  BasicBlock *faultBB = BasicBlock::Create(F->getContext(), "fault", F);

  //
  // Terminate the basic block with an unreachable instruction.
  //
  Instruction *UI = new UnreachableInst(F->getContext(), faultBB);

  //
  // Add an instruction that will generate a trap.
  //
  auto &C = F->getContext();
  auto *M = F->getParent();

  auto DummyFn =
      M->getOrInsertFunction("__softboundcets_dummy", Type::getVoidTy(C));
  CallInst::Create(DummyFn, "", UI);

  auto AbortFn =
      M->getOrInsertFunction("__softboundcets_abort", Type::getVoidTy(C));
  CallInst::Create(AbortFn, "", UI);

  return faultBB;
}

//
//
// Method: addSpatialChecks
//
// Description: This function inserts calls to C-handler spatial
// safety check functions and elides the check if the map says it is
// not necessary to check.

void SoftBoundCETSPass::addSpatialChecks(Instruction *load_store,
                                         std::map<Value *, int> &FDCE_map) {
  if (!ClSpatialSafety)
    return;

  SmallVector<Value *, 8> args;
  Value *pointer_operand = NULL;
  Type *pointee_type = NULL;

  if (LoadInst *ldi = dyn_cast<LoadInst>(load_store)) {
    if (!ClInsertSpatialLoadChecks)
      return;

    pointer_operand = ldi->getPointerOperand();
    pointee_type = ldi->getType();
  }

  if (StoreInst *sti = dyn_cast<StoreInst>(load_store)) {
    if (!ClInsertSpatialStoreChecks)
      return;

    pointer_operand = sti->getPointerOperand();
    pointee_type = sti->getValueOperand()->getType();
  }

  assert(pointer_operand && "pointer operand null?");

  if (!ClDisableSpatialCheckOpt) {
    if (ClEliminateStructChecks) {
      if (isStructOperand(pointer_operand)) {
        return;
      }
    }

    // If it is a null pointer which is being loaded, then it must seg
    // fault, no dereference check here

    if (isa<ConstantPointerNull>(pointer_operand))
      return;

    // Find all uses of pointer operand, then check if it dominates and
    // if so, make a note in the map

    GlobalVariable *gv = dyn_cast<GlobalVariable>(pointer_operand);
    if (gv && GLOBALCONSTANTOPT &&
        !(isa<ArrayType>(gv->getType()) || isa<VectorType>(gv->getType()))) {
      return;
    }

    if (BOUNDSCHECKOPT) {
      // Enable dominator based dereference check optimization only when
      // suggested

      if (FDCE_map.count(load_store)) {
        return;
      }

      // FIXME: Add more comments here Iterate over the uses

      for (Value::use_iterator ui = pointer_operand->use_begin(),
                               ue = pointer_operand->use_end();
           ui != ue; ++ui) {

        Instruction *temp_inst = dyn_cast<Instruction>(*ui);
        if (!temp_inst)
          continue;

        if (temp_inst == load_store)
          continue;

        if (!isa<LoadInst>(temp_inst) && !isa<StoreInst>(temp_inst))
          continue;

        if (isa<StoreInst>(temp_inst)) {
          if (temp_inst->getOperand(1) != pointer_operand) {
            // When a pointer is a being stored at at a particular
            // address, don't elide the check
            continue;
          }
        }

        if (m_dominator_tree->dominates(load_store, temp_inst)) {
          if (!FDCE_map.count(temp_inst)) {
            FDCE_map[temp_inst] = true;
            continue;
          }
        }
      } // Iterating over uses ends
    }   // BOUNDSCHECKOPT ends
  }

  Value *Base = NULL;
  Value *Bound = NULL;

  Constant *given_constant = dyn_cast<Constant>(pointer_operand);
  if (given_constant && GLOBALCONSTANTOPT)
    return;

  Base = getAssociatedBase(pointer_operand);
  Bound = getAssociatedBound(pointer_operand);

  if ((Base == MVoidNullPtr) && (Bound == MInfiniteBoundPtr))
    return;

  Value *bitcast_base = castToVoidPtr(Base, load_store);
  args.push_back(bitcast_base);

  Value *bitcast_bound = castToVoidPtr(Bound, load_store);
  args.push_back(bitcast_bound);

  Value *cast_pointer_operand_value =
      castToVoidPtr(pointer_operand, load_store);
  args.push_back(cast_pointer_operand_value);

  // Pushing the size of the type
  Value *size_of_type = getSizeOfType(pointee_type);
  args.push_back(size_of_type);

  if (isa<LoadInst>(load_store)) {

    CallInst::Create(SpatialLoadDereferenceCheckFn, args, "", load_store);
  } else {
    CallInst::Create(SpatialStoreDereferenceCheckFn, args, "", load_store);
  }

  return;
}

//
// Method: optimizeGlobalAndStackVariables
//
// Description: This function elides temporal safety checks for stack
// and global variables.

bool SoftBoundCETSPass::optimizeConstsGlobalAndStackVariableChecks(
    Instruction *load_store) {
  Value *pointer_operand = NULL;
  if (isa<LoadInst>(load_store)) {
    pointer_operand = load_store->getOperand(0);
  } else {
    pointer_operand = load_store->getOperand(1);
  }

  while (true) {
    if (isa<ConstantPointerNull>(pointer_operand))
      return true;

    if (isa<Constant>(pointer_operand))
      return true;

    if (isa<AllocaInst>(pointer_operand)) {
      if (STACKTEMPORALCHECKOPT) {
        return true;
      } else {
        return false;
      }
    }

    if (isa<GlobalVariable>(pointer_operand)) {
      if (GLOBALTEMPORALCHECKOPT) {
        return true;
      } else {
        return false;
      }
    }

    if (isa<BitCastInst>(pointer_operand)) {
      BitCastInst *bitcast_inst = dyn_cast<BitCastInst>(pointer_operand);
      pointer_operand = bitcast_inst->getOperand(0);
      continue;
    }

    if (isa<GetElementPtrInst>(pointer_operand)) {
      GetElementPtrInst *gep = dyn_cast<GetElementPtrInst>(pointer_operand);
      pointer_operand = gep->getOperand(0);
      continue;
    } else {
      return false;
    }
  }
}

//
// Method: bbTemporalCheckElimination
//
// Description: This function eliminates the redundant temporal safety
// checks in the basic block
//
// Comments: Describe the algorithm here

bool SoftBoundCETSPass::bbTemporalCheckElimination(
    Instruction *load_store, std::map<Value *, int> &BBTCE_map) {
  if (!BBDOMTEMPORALCHECKOPT)
    return false;

  if (BBTCE_map.count(load_store))
    return true;

  // Check if the operand is a getelementptr, then get the first
  // operand and check for all other load/store instructions in the
  // current basic block and check if they are pointer operands are
  // getelementptrs. If so, check if it is same the pointer being
  // checked now

  Value *pointer_operand = getPointerLoadStore(load_store);

  Value *gep_source = NULL;
  if (isa<GetElementPtrInst>(pointer_operand)) {
    GetElementPtrInst *ptr_gep = cast<GetElementPtrInst>(pointer_operand);
    gep_source = ptr_gep->getOperand(0);
  } else {
    gep_source = pointer_operand;
  }

  // Iterate over all other instructions in this basic block and look
  // for gep_instructions with the same source
  BasicBlock *bb_curr = load_store->getParent();
  assert(bb_curr && "bb null?");

  Instruction *next_inst = getNextInstruction(load_store);
  BasicBlock *next_inst_bb = next_inst->getParent();
  while ((next_inst_bb == bb_curr) && (next_inst != bb_curr->getTerminator())) {

    if (isa<CallInst>(next_inst) && OPAQUECALLS)
      break;

    if (checkLoadStoreSourceIsGEP(next_inst, gep_source)) {
      BBTCE_map[next_inst] = 1;
    }

    next_inst = getNextInstruction(next_inst);
    next_inst_bb = next_inst->getParent();
  }
  return false;
}
//
// Method:getPointerLoadStore
//
// Description: This function obtains the pointer operand which is
// being dereferenced in the memory access.

Value *SoftBoundCETSPass::getPointerLoadStore(Instruction *load_store) {
  Value *pointer_operand = NULL;
  if (isa<LoadInst>(load_store)) {
    pointer_operand = load_store->getOperand(0);
  }

  if (isa<StoreInst>(load_store)) {
    pointer_operand = load_store->getOperand(1);
  }
  assert((pointer_operand != NULL) && "pointer_operand null");
  return pointer_operand;
}

//
// Method : checkLoadSourceIsGEP
//
// Description: This function is used to optimize temporal checks by
// identifying the root object of the pointer being dereferenced.  If
// the pointer being deferenced is a bitcast or a GEP instruction then
// the source of GEP/bitcast is noted and checked to ascertain whether
// any check to the root object has been performed and not killed.
//
// Comments:
//
// TODO: A detailed algorithm here

bool SoftBoundCETSPass::checkLoadStoreSourceIsGEP(Instruction *load_store,
                                                  Value *gep_source) {
  Value *pointer_operand = NULL;

  if (!isa<LoadInst>(load_store) && !isa<StoreInst>(load_store))
    return false;

  if (isa<LoadInst>(load_store)) {
    pointer_operand = load_store->getOperand(0);
  }

  if (isa<StoreInst>(load_store)) {
    pointer_operand = load_store->getOperand(1);
  }

  assert(pointer_operand && "pointer_operand null?");

  if (!isa<GetElementPtrInst>(pointer_operand))
    return false;

  GetElementPtrInst *gep_ptr = dyn_cast<GetElementPtrInst>(pointer_operand);
  assert(gep_ptr && "gep_ptr null?");

  Value *gep_ptr_operand = gep_ptr->getOperand(0);

  if (gep_ptr_operand == gep_source)
    return true;

  return false;
}

//
// Method: funcTemporalCheckElimination
//
// Description: This function elides temporal checks for by performing
// root object identification at the function level.

bool SoftBoundCETSPass::funcTemporalCheckElimination(
    Instruction *load_store, std::map<Value *, int> &FTCE_map) {
  if (!FUNCDOMTEMPORALCHECKOPT)
    return false;

  if (FTCE_map.count(load_store))
    return true;

  Value *pointer_operand = getPointerLoadStore(load_store);

  Value *gep_source = NULL;
  if (isa<GetElementPtrInst>(pointer_operand)) {

    GetElementPtrInst *ptr_gep = dyn_cast<GetElementPtrInst>(pointer_operand);
    assert(ptr_gep && "[bbTemporalCheckElimination] gep_inst null?");
    gep_source = ptr_gep->getOperand(0);
  } else {
    gep_source = pointer_operand;
  }

  BasicBlock *bb_curr = load_store->getParent();
  assert(bb_curr && "bb null?");

  std::set<BasicBlock *> bb_visited;
  std::queue<BasicBlock *> bb_worklist;

  bb_worklist.push(bb_curr);
  BasicBlock *bb = NULL;
  while (bb_worklist.size() != 0) {

    bb = bb_worklist.front();
    assert(bb && "Not a BasicBlock?");

    bb_worklist.pop();
    if (bb_visited.count(bb)) {
      continue;
    }
    bb_visited.insert(bb);

    bool break_flag = false;

    // Iterating over the successors and adding the successors to the
    // work list

    // if this is the current basic block under question
    if (bb == bb_curr) {
      // bbTemporalCheckElimination should handle this
      Instruction *next_inst = getNextInstruction(load_store);
      BasicBlock *next_inst_bb = next_inst->getParent();
      while ((next_inst_bb == bb_curr) &&
             (next_inst != bb_curr->getTerminator())) {

        if (isa<CallInst>(next_inst) && OPAQUECALLS) {
          break_flag = true;
          break;
        }

        if (checkLoadStoreSourceIsGEP(next_inst, gep_source)) {
          if (m_dominator_tree->dominates(load_store, next_inst)) {
            FTCE_map[next_inst] = 1;
          }
        }

        next_inst = getNextInstruction(next_inst);
        next_inst_bb = next_inst->getParent();
      }
    } else {
      for (BasicBlock::iterator i = bb->begin(), ie = bb->end(); i != ie; ++i) {
        Instruction *new_inst = dyn_cast<Instruction>(i);
        if (isa<CallInst>(new_inst) && OPAQUECALLS) {
          break_flag = true;
          break;
        }

        if (checkLoadStoreSourceIsGEP(new_inst, gep_source)) {

          if (m_dominator_tree->dominates(load_store, new_inst)) {
            FTCE_map[new_inst] = 1;
          }
        }
      } // Iterating over the instructions in the basic block ends
    }

    for (succ_iterator si = succ_begin(bb), se = succ_end(bb); si != se; ++si) {

      if (break_flag)
        break;

      BasicBlock *next_bb = cast<BasicBlock>(*si);
      bb_worklist.push(next_bb);
    }
  } // Worklist algorithm ends
  return false;
}

bool SoftBoundCETSPass::optimizeTemporalChecks(
    Instruction *load_store, std::map<Value *, int> &BBTCE_map,
    std::map<Value *, int> &FTCE_map) {
  if (optimizeConstsGlobalAndStackVariableChecks(load_store))
    return true;

  if (bbTemporalCheckElimination(load_store, BBTCE_map))
    return true;

  if (funcTemporalCheckElimination(load_store, FTCE_map))
    return true;

  return false;
}

void SoftBoundCETSPass::addTemporalChecks(Instruction *load_store,
                                          std::map<Value *, int> &BBTCE_map,
                                          std::map<Value *, int> &FTCE_map) {
  SmallVector<Value *, 8> args;
  Value *pointer_operand = NULL;

  if (!ClTemporalSafety)
    return;

  if (!ClDisableTemporalCheckOpt) {
    if (optimizeTemporalChecks(load_store, BBTCE_map, FTCE_map))
      return;
  }

  if (isa<LoadInst>(load_store)) {
    if (!ClInsertTemporalLoadChecks)
      return;

    LoadInst *ldi = dyn_cast<LoadInst>(load_store);
    assert(ldi && "not a load instruction");
    pointer_operand = ldi->getPointerOperand();
  }

  if (isa<StoreInst>(load_store)) {
    if (!ClInsertTemporalStoreChecks)
      return;

    StoreInst *sti = dyn_cast<StoreInst>(load_store);
    assert(sti && "not a store instruction");
    // The pointer where the element is being stored is the second
    // operand
    pointer_operand = sti->getOperand(1);
  }

  assert(pointer_operand && "pointer_operand null?");

  if (!ClDisableTemporalCheckOpt) {
    /* Find all uses of pointer operand, then check if it
     * dominates and if so, make a note in the map
     */

    if (TEMPORALBOUNDSCHECKOPT) {
      /* Enable dominator based dereference check optimization only
       * when suggested
       */

      if (FTCE_map.count(load_store)) {
        return;
      }

      /* iterate over the uses */
      for (Value::use_iterator ui = pointer_operand->use_begin(),
                               ue = pointer_operand->use_end();
           ui != ue; ++ui) {

        Instruction *temp_inst = cast<Instruction>(*ui);
        if (!temp_inst)
          continue;

        if (temp_inst == load_store)
          continue;

        if (!isa<LoadInst>(temp_inst) && !isa<StoreInst>(temp_inst))
          continue;

        if (isa<StoreInst>(temp_inst)) {
          if (temp_inst->getOperand(1) != pointer_operand) {
            /* when a pointer is a being stored at at a particular
             * address, don't elide the check
             */
            continue;
          }
        }

        if (m_dominator_tree->dominates(load_store, temp_inst)) {
          if (!FTCE_map.count(temp_inst)) {
            FTCE_map[temp_inst] = true;
            continue;
          }
        }
      } /* Iterating over uses ends */
    }   /* TEMPORALBOUNDSCHECKOPT ends */
  }

  Value *Key = getAssociatedKey(pointer_operand);
  Value *Lock = getAssociatedLock(pointer_operand);

  auto *ConstantLock = dyn_cast<Constant>(Lock);
  // we do not need checks if we know its omnivalid metadata
  if (ConstantLock && (Key == MConstantIntOne) &&
      (MGlobalLockOnes.count(ConstantLock) > 0))
    return;

  args.push_back(Lock);

  args.push_back(Key);

#ifdef SOFTBOUNDCETS_CHK_INTRINSIC

  if (ClInsertCheckIntrinsics) {
    Module *M = load_store->getParent()->getParent()->getParent();
    Type *Tys[] = {m_void_ptr_type, m_key_type, m_void_ptr_type,
                   m_void_ptr_type};
    Function *temporal_chk_function =
        Intrinsic::getDeclaration(M, Intrinsic::sbcets_temporalchk, Tys);

    CallInst::Create(temporal_chk_function, args, "", load_store);

    return;
  }
#endif

  if (isa<LoadInst>(load_store)) {
    CallInst::Create(TemporalLoadDereferenceCheckFn, args, "", load_store);
  } else {
    CallInst::Create(TemporalStoreDereferenceCheckFn, args, "", load_store);
  }
  return;
}

void SoftBoundCETSPass::addDereferenceChecks(Function *func) {
  Function &F = *func;

  if (func->isVarArg())
    return;

  if (ClPropagateMetadataOnly)
    return;

  if (Blacklist &&
      Blacklist->inSection("softboundcets", "fun", func->getName(), "*"))
    return;

  std::vector<Instruction *> CheckWorkList;
  std::map<Value *, bool> ElideSpatialCheck;
  std::map<Value *, bool> ElideTemporalCheck;

  // identify all the instructions where we need to insert the spatial checks
  for (inst_iterator i = inst_begin(F), e = inst_end(F); i != e; ++i) {

    Instruction *I = &*i;

    if (!MPresentInOriginal.count(I)) {
      continue;
    }
    // add check optimizations here
    // add checks for memory fences and atomic exchanges
    if (isa<LoadInst>(I) || isa<StoreInst>(I)) {
      CheckWorkList.push_back(I);
    }
    if (isa<AtomicCmpXchgInst>(I) || isa<AtomicRMWInst>(I)) {
      assert(0 && "Atomic Instructions not handled");
    }
  }

#if 0
  // spatial check optimizations here 

  for(std::vector<Instruction*>::iterator i = CheckWorkList.begin(), 
	e = CheckWorkList.end(); i!= e; ++i){

    Instruction* inst = *i;
    Value* pointer_operand = NULL;
    
    if(ElideSpatialCheck.count(inst))
      continue;
    
    if(isa<LoadInst>(inst)){
      LoadInst* ldi = dyn_cast<LoadInst>(inst);
      pointer_operand = ldi->getPointerOperand();
    }
    if(isa<StoreInst>(inst)){
      StoreInst* st = dyn_cast<StoreInst>(inst);
      pointer_operand = st->getOperand(1);      
    }

    for(Value::use_iterator ui = pointer_operand->use_begin(),  
	  ue = pointer_operand->use_end();
	ui != ue; ++ui){

      Instruction* use_inst = dyn_cast<Instruction>(*ui);
      if(!use_inst || (use_inst == inst))
	continue;

      if(!isa<LoadInst>(use_inst)  && !isa<StoreInst>(use_inst))
	continue;

      if(isa<StoreInst>(use_inst)){
	if(use_inst->getOperand(1) != pointer_operand)
	  continue;
      }

      if(m_dominator_tree->dominates(inst, use_inst)){
	if(!ElideSpatialCheck.count(use_inst))
	  ElideSpatialCheck[use_inst] = true;		
      }
    }  
  }

#endif

  // Temporal Check Optimizations

#ifdef INSERT_CHECKS_DIRECTLY
  // the following code adds checks directly into the program. It bypasses the
  // *_check functions in the runtime library. This can be helpful if LTO does
  // not work properly
  for (std::vector<Instruction *>::iterator i = CheckWorkList.begin(),
                                            e = CheckWorkList.end();
       i != e; ++i) {

    Instruction *Inst = *i;

    Value *pointer_operand = NULL;

    if (isa<LoadInst>(Inst)) {
      LoadInst *ldi = dyn_cast<LoadInst>(Inst);
      pointer_operand = ldi->getPointerOperand();
    }

    if (isa<StoreInst>(Inst)) {
      StoreInst *st = dyn_cast<StoreInst>(Inst);
      pointer_operand = st->getOperand(1);
    }

    if (isa<ConstantExpr>(pointer_operand))
      continue;

    Value *pointer_base = getAssociatedBase(pointer_operand);
    Value *pointer_bound = getAssociatedBound(pointer_operand);

    Value *pointer_key = getAssociatedKey(pointer_operand);
    Value *pointer_lock = getAssociatedLock(pointer_operand);

    Builder->SetInsertPoint(Inst);

    Value *cast_pointer_lock =
        Builder->CreateBitCast(pointer_lock, m_sizet_ptr_type);
    Value *lock_load = Builder->CreateLoad(cast_pointer_lock, "");
    Value *cmp_eq = Builder->CreateICmpNE(pointer_key, lock_load);

    Value *cast_pointer =
        Builder->CreateBitCast(pointer_operand, m_void_ptr_type);

    Value *sizeofType = getSizeOfType(pointer_operand->getType());

    Value *Cmp1 = Builder->CreateICmpULT(cast_pointer, pointer_base);
    Value *sub = Builder->CreatePtrDiff(pointer_bound, cast_pointer);

    Value *Cmp2 = Builder->CreateICmpUGT(sizeofType, sub);

    Value *Or = Builder->CreateOr(Cmp1, Cmp2);

    Value *Or2 = Builder->CreateOr(Or, cmp_eq);

#if 0
    FunctionCallee call_print_metadata = Inst->getParent()->getParent()->getParent()->getOrInsertFunction("__softboundcets_print_metadata");
    Builder->CreateCall(call_print_metadata, {pointer_base, pointer_bound, cast_pointer, pointer_key, cast_pointer_lock});

    FunctionCallee intermediate = Inst->getParent()->getParent()->getParent()->getOrInsertFunction("__softboundcets_intermediate");
    Builder->CreateCall(intermediate, {Cmp1, Cmp2, cmp_eq, lock_load});
#endif

    BasicBlock *OldBB = Inst->getParent();
    BasicBlock *Cont = OldBB->splitBasicBlock(Inst);
    OldBB->getTerminator()->eraseFromParent();

    assert(m_faulting_block.count(Inst->getParent()->getParent()));
    BasicBlock *faultBB = m_faulting_block[Inst->getParent()->getParent()];

    BranchInst::Create(faultBB, Cont, Or2, OldBB);

    continue;
  }

  return;
#endif

  m_dominator_tree = &getAnalysis<DominatorTreeWrapperPass>(*func).getDomTree();

  /* intra-procedural load dererference check elimination map */
  std::map<Value *, int> func_deref_check_elim_map;
  std::map<Value *, int> func_temporal_check_elim_map;

  /* WorkList Algorithm for adding dereference checks. Each basic
   * block is visited only once. We start by visiting the current
   * basic block, then pushing all the successors of the current
   * basic block on to the queue if it has not been visited
   */

  std::set<BasicBlock *> bb_visited;
  std::queue<BasicBlock *> bb_worklist;
  Function::iterator bb_begin = func->begin();

  BasicBlock *bb = dyn_cast<BasicBlock>(bb_begin);
  assert(bb && "Not a basic block  and I am adding dereference checks?");
  bb_worklist.push(bb);

  while (bb_worklist.size() != 0) {

    bb = bb_worklist.front();
    assert(bb && "Not a BasicBlock?");
    bb_worklist.pop();

    if (bb_visited.count(bb)) {
      /* Block already visited */
      continue;
    }

    /* If here implies basic block not visited */
    /* Insert the block into the set of visited blocks */
    bb_visited.insert(bb);

    /* Iterating over the successors and adding the successors to
     * the worklist
     */
    for (succ_iterator si = succ_begin(bb), se = succ_end(bb); si != se; ++si) {

      BasicBlock *next_bb = *si;
      assert(
          next_bb &&
          "Not a basic block and I am adding to the base and bound worklist?");
      bb_worklist.push(next_bb);
    }

    /* basic block load deref check optimization */
    std::map<Value *, int> bb_deref_check_map;
    std::map<Value *, int> bb_temporal_check_elim_map;
    /* structure check optimization */
    std::map<Value *, int> bb_struct_check_opt;

    for (BasicBlock::iterator i = bb->begin(), ie = bb->end(); i != ie; ++i) {
      Value *v1 = dyn_cast<Value>(i);
      Instruction *new_inst = dyn_cast<Instruction>(i);

      /* Do the dereference check stuff */
      if (!MPresentInOriginal.count(v1))
        continue;

      if (isa<LoadInst>(new_inst) || isa<StoreInst>(new_inst)) {

        addSpatialChecks(new_inst, func_deref_check_elim_map);
        addTemporalChecks(new_inst, bb_temporal_check_elim_map,
                          func_temporal_check_elim_map);
        continue;
      }

      /* check call through function pointers */
      if (CALLCHECKS && isa<CallInst>(new_inst)) {

        SmallVector<Value *, 8> args;
        CallInst *call_inst = dyn_cast<CallInst>(new_inst);
        Value *tmp_base = NULL;
        Value *tmp_bound = NULL;

        assert(call_inst && "call instruction null?");

        if (!INDIRECTCALLCHECKS)
          continue;

        /* TODO:URGENT : indirect function call checking commented
         * out for the time being to test other aspect of the code,
         * problem was with spec benchmarks perl and h264. They were
         * primarily complaining that the use of a function did not
         * have base and bound in the map
         */

        /* here implies its an indirect call */
        Value *indirect_func_called = call_inst->getOperand(0);

        Constant *func_constant = dyn_cast<Constant>(indirect_func_called);
        if (func_constant) {
          getConstantExprBaseBound(func_constant, tmp_base, tmp_bound);
        } else {
          tmp_base = getAssociatedBase(indirect_func_called);
          tmp_bound = getAssociatedBound(indirect_func_called);
        }
        /* Add BitCast Instruction for the base */
        Value *bitcast_base = castToVoidPtr(tmp_base, new_inst);
        args.push_back(bitcast_base);

        /* Add BitCast Instruction for the bound */
        Value *bitcast_bound = castToVoidPtr(tmp_bound, new_inst);
        args.push_back(bitcast_bound);
        Value *pointer_operand_value =
            castToVoidPtr(indirect_func_called, new_inst);
        args.push_back(pointer_operand_value);
        CallInst::Create(CallDereferenceCheckFn, args, "", new_inst);
        continue;
      } /* Call check ends */
    }
  }
}

void SoftBoundCETSPass::renameFunctions(Module &module) {
  bool change = false;

  do {
    change = false;
    for (Module::iterator ff_begin = module.begin(), ff_end = module.end();
         ff_begin != ff_end; ++ff_begin) {

      Function *func_ptr = dyn_cast<Function>(ff_begin);

      if (m_func_transformed.count(func_ptr->getName()) ||
          isFunctionNotToInstrument(func_ptr->getName())) {
        continue;
      }

      m_func_transformed[func_ptr->getName()] = true;
      m_func_transformed[transformFunctionName(func_ptr->getName().str())] =
          true;
      bool is_external = func_ptr->isDeclaration();
      renameFunctionName(func_ptr, module, is_external);
      change = true;
      break;
    }
  } while (change);
}

/* Renames a function by changing the function name to softboundcets_*
   for only those functions have wrappers
 */

void SoftBoundCETSPass::renameFunctionName(Function *F, Module &M,
                                           bool External) {
  Type *RetTy = F->getReturnType();
  const FunctionType *FTy = F->getFunctionType();
  std::vector<Type *> Params;
  auto FName = F->getName();

  if (!MFunctionWrappersAvailable.count(FName))
    return;

  LLVM_DEBUG(dbgs() << "\n======================\nWrapping function with "
                       "SBCETS runtime handler: "
                    << FName << "\n");

  SmallVector<AttributeSet, 8> ParamAttrsVec;

  // #if 0

  //   const AttrListPtr& pal = F->getAttributes();
  //   if(Attributes attrs = pal.getRetAttributes())
  //     param_attrs_vec.push_back(AttributeWithIndex::get(0, attrs));
  // #endif

  for (Argument &Arg : F->args()) {

    Params.push_back(Arg.getType());
    // #if 0
    //     if(Attributes attrs = pal.getParamAttributes(arg_index))
    //       param_attrs_vec.push_back(AttributeWithIndex::get(params.size(),
    //       attrs));
    // #endif
  }

  // check if we have loaded the rt-lib bitcode into the module already
  auto *FunctionWrapper = M.getFunction(transformFunctionName(FName.str()));

  // if not, we create a function declaration which can be resolved during
  // linking
  if (!FunctionWrapper) {
    FunctionType *FWrapperTy =
        FunctionType::get(RetTy, Params, FTy->isVarArg());
    FunctionWrapper = Function::Create(FWrapperTy, F->getLinkage(),
                                       transformFunctionName(FName.str()));
    FunctionWrapper->copyAttributesFrom(F);
    F->getParent()->getFunctionList().push_back(FunctionWrapper);
  }

  // reimplement doRAUW for Constant Users of Function
  // where we want to replace the Function with the FunctionWrapper
  // NOTE: replaceUsesWithIf does not work for Constants
  for (auto UI = F->use_begin(), E = F->use_end(); UI != E;) {
    Use &U = *UI;
    ++UI;

    if (auto *C = dyn_cast<Constant>(U.getUser())) {
      if (!isa<GlobalValue>(C)) {
        C->handleOperandChange(F, FunctionWrapper);
        continue;
      }
      U.set(FunctionWrapper);
    }
  }

  F->replaceUsesWithIf(FunctionWrapper, [this](Use &U) -> bool {
    auto *Usr = U.getUser();
    auto *I = dyn_cast<Instruction>(Usr);
    if (I) {
      return InstrumentedFunctions.contains(I->getFunction());
    }
    return false;
  });
}

void SoftBoundCETSPass::handleAlloca(AllocaInst *AI, Value *Key, Value *Lock,
                                     Value *func_xmm_key_lock) {
  if (ClSpatialSafety) {
    auto *InsertPoint = AI->getNextNode();
    assert(InsertPoint && "Alloca is the last instruction in the basic block?");
    IRBuilder<> IRB(InsertPoint);

    // For any alloca, the base is a bitcast of the alloca and the bound is a
    // bitcast of alloca + 1.
    Value *Base = castToVoidPtr(AI, IRB);

    Value *Idx;
    if (AI->getNumOperands() == 0) {
      if (m_is_64_bit) {
        Idx = ConstantInt::get(Type::getInt64Ty(AI->getType()->getContext()), 1,
                               false);
      } else {
        Idx = ConstantInt::get(Type::getInt32Ty(AI->getType()->getContext()), 1,
                               false);
      }
    } else {
      Idx = AI->getOperand(0);
    }

    Value *Bound = IRB.CreateGEP(AI->getAllocatedType(), AI, Idx, "mtmp");
    Bound = castToVoidPtr(Bound, IRB);

    associateBaseBound(AI, Base, Bound);
  }

  if (ClTemporalSafety) {
    associateKeyLock(AI, Key, Lock);
  }
}

void SoftBoundCETSPass::handleVectorStore(StoreInst *Store) {
  Value *Val = Store->getOperand(0);
  Value *StoreDest = Store->getOperand(1);
  Instruction *InsertAt = getNextInstruction(Store);

  SmallVector<Value *, 8> ExtractedBases, ExtractedBounds, ExtractedKeys,
      ExtractedLocks;

  if (ClSpatialSafety) {
    ExtractedBases = extractVectorBases(Val, InsertAt);
    ExtractedBounds = extractVectorBounds(Val, InsertAt);
  }
  if (ClTemporalSafety) {
    ExtractedKeys = extractVectorKeys(Val, InsertAt);
    ExtractedLocks = extractVectorLocks(Val, InsertAt);
  }

  const VectorType *VectorTy = dyn_cast<VectorType>(Val->getType());
  ElementCount NumElements = VectorTy->getElementCount();

  Value *PtrOpBitcast = castToVoidPtr(StoreDest, InsertAt);
  SmallVector<Value *, 8> Args;
  for (uint64_t i = 0; i < NumElements.getValue(); i++) {

    Args.clear();
    Constant *Idx = ConstantInt::get(Type::getInt32Ty(Store->getContext()), i);
    Args.push_back(PtrOpBitcast);

    if (ClSpatialSafety) {
      Value *PtrBase = ExtractedBases[i];
      Value *PtrBound = ExtractedBounds[i];
      Args.push_back(PtrBase);
      Args.push_back(PtrBound);
    }
    if (ClTemporalSafety) {
      Value *PtrKey = ExtractedKeys[i];
      Value *PtrLock = ExtractedLocks[i];
      Args.push_back(PtrKey);
      Args.push_back(PtrLock);
    }

    Args.push_back(Idx);

    CallInst::Create(StoreVectorMetadataFn, Args, "", InsertAt);
  }
}

// handles vector which contains pointers
// iterates over each element of vector and inserts function call to load
// metadata of pointer via LUT this metadata is then carried around with the
// vector in a separate vector we need to use other vectors as we otherwise
// cannot associate the pointer extracted from the vector at runtime with its
// metadata as we don't know at compile time the index of the extractelement
// instruction
void SoftBoundCETSPass::handleVectorLoad(LoadInst *Load) {

  // It should be a fixed vector if here
  const FixedVectorType *VectorTy = cast<FixedVectorType>(Load->getType());

  Value *PointerOp = Load->getPointerOperand();
  Instruction *InsertAt = getNextInstruction(Load);

  Instruction *FirstFunctionInst =
      dyn_cast<Instruction>(Load->getParent()->getParent()->begin()->begin());
  assert(FirstFunctionInst &&
         "function doesn't have any instruction and there is load???");

  uint64_t NumElements = VectorTy->getElementCount().getValue();

  SoftBoundCETSMetadata Metadata;

  insertVectorMetadataLoad(PointerOp, Metadata, InsertAt, NumElements);

  if (ClSpatialSafety)
    associateBaseBound(Load, Metadata.Base, Metadata.Bound);

  if (ClTemporalSafety)
    associateKeyLock(Load, Metadata.Key, Metadata.Lock);
}

void SoftBoundCETSPass::handleAggregateStore(StoreInst *Store) {
  Value *StoreVal = Store->getOperand(0);
  Type *StoreValTy = StoreVal->getType();
  Value *StoreDest = Store->getOperand(1);
  Instruction *InsertAt = getNextInstruction(Store);
  /** (ds)
   *  When writing a aggregate with pointers to memory,
   *  the metadata for each contained pointer is stored in the runtime
   * datastructure. Therefore we must compute the addresses of each pointer
   * after being stored. This is achieved by generating GEP instructions using
   * the store destination as base. Finally, a call to store metadata in the
   * runtime is generated for each pointer.
   */

  // generate GEPs for each contained pointer
  SmallVector<Value *, 8> GEPs;

  generateAggregateGEPs(StoreDest, StoreValTy, InsertAt, GEPs);

  ArrayRef<Value *> Bases = getAssociatedBases(StoreVal);
  ArrayRef<Value *> Bounds = getAssociatedBounds(StoreVal);
  ArrayRef<Value *> Keys = getAssociatedKeys(StoreVal);
  ArrayRef<Value *> Locks = getAssociatedLocks(StoreVal);

  assert(Bases.size() == GEPs.size() && Bounds.size() == GEPs.size() &&
         Keys.size() == GEPs.size() && Locks.size() == GEPs.size() &&
         "The number of metadata entries must match the number of generated "
         "GEPs");

  for (unsigned J = 0; J < GEPs.size(); ++J) {
    auto *GEP = GEPs[J];
    auto *GEPElementTy = cast<PointerType>(GEP->getType())->getElementType();
    if (GEPElementTy->isVectorTy()) {
      insertVectorMetadataStore(GEP, Bases[J], Bounds[J], Keys[J], Locks[J],
                                InsertAt);
    } else {
      insertPointerMetadataStore(GEP, Bases[J], Bounds[J], Keys[J], Locks[J],
                                 InsertAt);
    }
  }
}

void SoftBoundCETSPass::handleStore(StoreInst *Store) {
  Value *StoreVal = Store->getOperand(0);
  Type *StoreValTy = StoreVal->getType();
  Value *StoreDest = Store->getOperand(1);
  Instruction *InsertAt = getNextInstruction(Store);
  if (!isTypeWithPointers(StoreValTy))
    return;

  /* If a pointer is being stored, then the base and bound
   * corresponding to the pointer must be stored in the shadow space
   */

  /* if it is a global expression being stored, then add add
   * suitable base and bound
   */

  if (isVectorWithPointers(StoreValTy)) {
    handleVectorStore(Store);
  } else if (isa<PointerType>(StoreValTy)) {
    Value *Base = NULL;
    Value *Bound = NULL;
    if (ClSpatialSafety) {
      Base = getAssociatedBase(StoreVal);
      Bound = getAssociatedBound(StoreVal);
    }

    Value *Key = NULL;
    Value *Lock = NULL;
    if (ClTemporalSafety) {
      Key = getAssociatedKey(StoreVal);
      Lock = getAssociatedLock(StoreVal);
    }

    insertPointerMetadataStore(StoreDest, Base, Bound, Key, Lock, InsertAt);
  } else if (StoreValTy->isAggregateType()) {
    handleAggregateStore(Store);
  } else {
    assert(0 && "Storing value with pointers that is unhandled");
  }
}

// Currently just a placeholder for functions introduced by us
bool SoftBoundCETSPass::checkIfFunctionOfInterest(Function *func) {
  if (isFunctionNotToInstrument(func->getName()))
    return false;

  if (func->isDeclaration())
    return false;

    /* TODO: URGENT: Need to do base and bound propagation in variable
     * argument functions
     */
#if 0
  if(func.isVarArg())
    return false;
#endif

  return true;
}

Instruction *SoftBoundCETSPass::getGlobalsInitializerInsertPoint(Module &M) {
  Function *GlobalsInitFn = M.getFunction(kSoftBoundCETSGlobalsInitializerName);

  if (!GlobalsInitFn) {
    // Create the globals initializer and call it from our global constructor.
    auto *CtorFn = M.getFunction(kSoftBoundCETSCtorName);
    assert(CtorFn && "Global constructor not inserted?");
    GlobalsInitFn =
        createSanitizerCtor(M, kSoftBoundCETSGlobalsInitializerName);
    IRBuilder<> IRB(CtorFn->getEntryBlock().getTerminator());
    IRB.CreateCall(GlobalsInitFn, {});
  }

  return GlobalsInitFn->getEntryBlock().getTerminator();
}

bool SoftBoundCETSPass::isVaargGep(GetElementPtrInst *GepInst) {
  /* (av)
    We want to identify all getelementptr instructions that load the
    pointer to overflow_arg_area or the reg_save_area. That is e.g.
    %0 = getelementptr inbounds %struct.__va_list_tag, %struct.__va_list_tag*
    %arraydecay2, i32 0, i32 3 or %overflow_arg_area_p = getelementptr inbounds
    %struct.__va_list_tag, %struct.__va_list_tag* %arraydecay2, i32 0, i32 2 As
    this struct could be part of another struct or array, we have to iteratively
    follow the indices of the instruction.
  */

  // return false;
  auto GEPIndices = GepInst->getNumIndices();
  if (GEPIndices < 2)
    return false;

  auto *CompTy = GepInst->getSourceElementType();

  auto *Idx = GepInst->idx_begin();

  Value *ThirdLastIdx = NULL;
  Value *SecondLastIdx = *Idx;

  Idx++;

  for (unsigned int NextIndexPos = 2; Idx != GepInst->idx_end();
       Idx++, NextIndexPos++) {

    if (!CompTy)
      return false;

    // integer value of index
    uint64_t LastIndex = dyn_cast<ConstantInt>(*Idx)
                             ? dyn_cast<ConstantInt>(*Idx)->getZExtValue()
                             : 0;

    // stop if we followed all but the last two indices
    // check if the second to last is 0 and the last is 2 or 3
    if (NextIndexPos >= GEPIndices) {
      if (LastIndex != 2 && LastIndex != 3)
        return false;
      break;
    }

    ThirdLastIdx = SecondLastIdx;
    SecondLastIdx = *Idx;

    if (NextIndexPos > 1) {
      CompTy = GetElementPtrInst::getTypeAtIndex(CompTy, ThirdLastIdx);
    }
  }

  StructType *StTy = dyn_cast_or_null<StructType>(CompTy);

  return StTy && StTy->hasName() &&
         StTy->getName().contains("struct.__va_list_tag");
}

void SoftBoundCETSPass::varargAssociatePointerLoads(Instruction *VarArgInst) {

  SmallVector<LoadInst *> LoadInsts;
  std::set<Value *> Visited;
  collectVarargPointerLoads(VarArgInst, LoadInsts, Visited);

  for (auto *LI : LoadInsts) {
    associateOmnivalidMetadata(LI);
  }
}

void SoftBoundCETSPass::handleGEP(GetElementPtrInst *GEP) {
  Value *GEPPtrOp = GEP->getPointerOperand();
  // we need to account for
  // https://llvm.org/docs/LangRef.html#vector-of-pointers: in short; if a
  // vector of offsets is used as indices, the result of the GEP is a vector. As
  // we do not calculate subbounds for gep vectors, we need to associate each pointer in the
  // resulting vector with the metadata of the GEPPtrOp
  FixedVectorType *FixedVectorTy = dyn_cast<FixedVectorType>(GEP->getType());
  if (FixedVectorTy && !isa<FixedVectorType>(GEPPtrOp->getType())) {
    auto VectorSize = FixedVectorTy->getElementCount().getValue();
    if (ClSpatialSafety) {
      auto *Base = getAssociatedBase(GEPPtrOp);
      auto *Bound = getAssociatedBound(GEPPtrOp);
      SmallVector<Value *> Bases(VectorSize, Base);
      SmallVector<Value *> Bounds(VectorSize, Bound);
      auto *BaseVector = createMetadataVector(Bases, GEP);
      auto *BoundVector = createMetadataVector(Bounds, GEP);
      associateBaseBound(GEP, BaseVector, BoundVector);
    }
    if (ClTemporalSafety) {
      auto *Key = getAssociatedKey(GEPPtrOp);
      auto *Lock = getAssociatedLock(GEPPtrOp);
      SmallVector<Value *> Keys(VectorSize, Key);
      SmallVector<Value *> Locks(VectorSize, Lock);
      auto *KeyVector = createMetadataVector(Keys, GEP);
      auto *LockVector = createMetadataVector(Locks, GEP);
      associateKeyLock(GEP, KeyVector, LockVector);
    }
  } else if (ClIntraObjectBounds && !FixedVectorTy) {

    auto *GEPSrcTy = GEP->getSourceElementType();

    // only narrow bounds if the GEP indexes a struct or a vector
    // as detailed in the original paper, we don't want to narrow bounds if we
    // index an array or only the pointer
    bool GEPIndexesOnlyPtrAndArrays = true;
    if (GEPSrcTy->isStructTy() || GEPSrcTy->isVectorTy()) {
      if (GEP->getNumIndices() > 1)
        GEPIndexesOnlyPtrAndArrays = false;
    }

    std::vector<Value *> GEPIndices(GEP->idx_begin(), GEP->idx_end());
    for (; (GEPIndices.size() > 2); GEPIndices.pop_back()) {

      auto IndexSlice =
          std::vector<Value *>(GEPIndices.begin() + 1, GEPIndices.end() - 1);
      auto *IndexedTy = GetElementPtrInst::getIndexedType(GEPSrcTy, GEPIndices);

      if (IndexedTy->isStructTy() || IndexedTy->isVectorTy()) {
        GEPIndexesOnlyPtrAndArrays = false;
        break;
      }
    }

    if (!GEPIndexesOnlyPtrAndArrays) {

      IRBuilder<> IRB(getNextInstruction(GEP));

      // Calculate max(original base of GEPPtrOp, GEP)
      auto *OriginalBase = getAssociatedBase(GEPPtrOp);
      // we use the GEP as Base if we haven't removed any indices.
      // otherwise we create a new GEP for the base
      auto *GEPBase = (GEPIndices.size() == GEP->getNumIndices())
                          ? GEP
                          : IRB.CreateGEP(GEPSrcTy, GEPPtrOp, GEPIndices);
      auto *GEPCast =
          IRB.CreateBitCast(GEPBase, MVoidPtrTy, GEP->getName() + ".voidptr");
      auto *CmpBases = IRB.CreateICmpUGT(OriginalBase, GEPCast);
      auto *NewBase = IRB.CreateSelect(CmpBases, OriginalBase, GEPCast);

      // Calculate min(original bound of GEPPtrOp, GEP+1)
      auto *OriginalBound = getAssociatedBound(GEPPtrOp);
      auto *GEPBound = IRB.CreateGEP(GEPBase, IRB.getInt32(1));
      auto *GEPBoundCast =
          IRB.CreateBitCast(GEPBound, MVoidPtrTy, GEP->getName() + ".voidptr");
      auto *CmpBounds = IRB.CreateICmpULT(OriginalBound, GEPBoundCast);
      auto *NewBound = IRB.CreateSelect(CmpBounds, OriginalBound, GEPBoundCast);

      associateBaseBound(GEP, NewBase, NewBound);

      auto *Key = getAssociatedKey(GEPPtrOp);
      auto *Lock = getAssociatedLock(GEPPtrOp);
      associateKeyLock(GEP, Key, Lock);
    } else
      propagateMetadata(GEPPtrOp, GEP);
  } else
    propagateMetadata(GEPPtrOp, GEP);
}

void SoftBoundCETSPass::handleShuffleVector(ShuffleVectorInst *SV) {
  auto *V0 = SV->getOperand(0);
  auto *V1 = SV->getOperand(0);
  auto Mask = SV->getShuffleMask();

  if (ClSpatialSafety) {
    auto *Bases0 = getAssociatedBase(V0);
    auto *Bases1 = getAssociatedBase(V1);
    auto *Bounds0 = getAssociatedBound(V0);
    auto *Bounds1 = getAssociatedBound(V1);

    auto *NewBases =
        new ShuffleVectorInst(Bases0, Bases1, Mask, "shuffle_vector.bases", SV);
    auto *NewBounds = new ShuffleVectorInst(Bounds0, Bounds1, Mask,
                                            "shuffle_vector.bounds", SV);
    associateBaseBound(SV, NewBases, NewBounds);
  }
  if (ClTemporalSafety) {
    auto *Keys0 = getAssociatedKey(V0);
    auto *Keys1 = getAssociatedKey(V1);
    auto *Locks0 = getAssociatedLock(V0);
    auto *Locks1 = getAssociatedLock(V1);

    auto *NewKeys =
        new ShuffleVectorInst(Keys0, Keys1, Mask, "shuffle_vector.keys", SV);
    auto *NewLocks =
        new ShuffleVectorInst(Locks0, Locks1, Mask, "shuffle_vector.locks", SV);
    associateKeyLock(SV, NewKeys, NewLocks);
  }
}

void SoftBoundCETSPass::handleMaskedVectorLoad(CallBase *CB) {

  auto *InsertAt = getNextInstruction(CB);
  IRBuilder<> IRB(InsertAt);

  auto *LoadSrc = CB->getArgOperand(0);
  auto *LoadSrcBitcast = castToVoidPtr(LoadSrc, InsertAt);

  auto *Mask = CB->getArgOperand(2);
  auto *MaskTy = dyn_cast<FixedVectorType>(Mask->getType());
  auto VecSize = MaskTy->getNumElements();
  auto *PassThru = CB->getArgOperand(3);

  SmallVector<Value *, 8> Bases;
  SmallVector<Value *, 8> Bounds;
  SmallVector<Value *, 8> Keys;
  SmallVector<Value *, 8> Locks;

  for (unsigned VecIdx = 0; VecIdx < VecSize; VecIdx++) {

    ConstantInt *IdxArg = ConstantInt::get(Type::getInt32Ty(*C), VecIdx);
    Value *MaskValAtIdx =
        ExtractElementInst::Create(Mask, IdxArg, "", InsertAt);

    SmallVector<Value *, 8> Args;

    Args.push_back(LoadSrcBitcast);

    Args.push_back(IdxArg);
    Args.push_back(MaskValAtIdx);

    if (ClSimpleMetadataMode) {
      if (ClSpatialSafety) {
        Value *Base = CallInst::Create(MaskedLoadVectorMetadataBaseFn, Args, "",
                                       InsertAt);
        Value *Bound = CallInst::Create(MaskedLoadVectorMetadataBoundFn, Args,
                                        "", InsertAt);
        Bases.push_back(Base);
        Bounds.push_back(Bound);
      }
      if (ClTemporalSafety) {
        Value *Lock = CallInst::Create(MaskedLoadVectorMetadataLockFn, Args, "",
                                       InsertAt);
        Value *Key =
            CallInst::Create(MaskedLoadVectorMetadataKeyFn, Args, "", InsertAt);

        Keys.push_back(Key);
        Locks.push_back(Lock);
      }

    } else {

      auto *MetadataPtr = IRB.CreateCall(LoadMaskedVectorMetadataPtrFn, Args);

      unsigned KeyIdx = 0;
      unsigned LockIdx = 1;

      if (ClSpatialSafety) {
        auto *BasePtr = IRB.CreateStructGEP(MetadataPtr, 0, "baseptr");
        Value *Base = IRB.CreateLoad(BasePtr, "base");
        Bases.push_back(Base);
        auto *BoundPtr = IRB.CreateStructGEP(MetadataPtr, 1, "boundptr");
        Value *Bound = IRB.CreateLoad(BoundPtr, "bound");
        Bounds.push_back(Bound);

        KeyIdx = 2;
        LockIdx = 3;
      }
      if (ClTemporalSafety) {
        auto *KeyPtr = IRB.CreateStructGEP(MetadataPtr, KeyIdx, "keyptr");
        Value *Key = IRB.CreateLoad(KeyPtr, "key");
        Keys.push_back(Key);
        auto *LockPtr = IRB.CreateStructGEP(MetadataPtr, LockIdx, "lockptr");
        Value *Lock = IRB.CreateLoad(LockPtr, "lock");
        Locks.push_back(Lock);
      }
    }
  }

  if (ClSpatialSafety) {
    auto *VecBase = createMetadataVector(Bases, InsertAt);
    auto *VecBound = createMetadataVector(Bounds, InsertAt);
    auto *PassthruBase = getAssociatedBase(PassThru);
    auto *PassthruBound = getAssociatedBound(PassThru);

    auto *SelectBase = SelectInst::Create(Mask, VecBase, PassthruBase,
                                          "select.masked.load.base", InsertAt);
    auto *SelectBound = SelectInst::Create(Mask, VecBound, PassthruBound,
                                           "select.masked.load.base", InsertAt);
    associateBaseBound(CB, SelectBase, SelectBound);
  }
  if (ClTemporalSafety) {
    auto *VecKey = createMetadataVector(Keys, InsertAt);
    auto *VecLock = createMetadataVector(Locks, InsertAt);
    auto *PassthruKey = getAssociatedKey(PassThru);
    auto *PassthruLock = getAssociatedLock(PassThru);

    auto *SelectKey = SelectInst::Create(Mask, VecKey, PassthruKey,
                                         "select.masked.load.base", InsertAt);
    auto *SelectLock = SelectInst::Create(Mask, VecLock, PassthruLock,
                                          "select.masked.load.base", InsertAt);
    associateKeyLock(CB, SelectKey, SelectLock);
  }
}

void SoftBoundCETSPass::handleMemcpy(CallBase *CB) {
  if (DISABLE_MEMCOPY_METADATA_COPIES)
    return;

  Function *F = CB->getCalledFunction();
  if (!F)
    return;

  assert(F && "function is null?");

  Value *Arg0 = CB->getArgOperand(0);
  Value *Arg1 = CB->getArgOperand(1);
  Value *Arg2 = CB->getArgOperand(2);

  SmallVector<Value *, 8> Args;
  Args.push_back(Arg0);
  Args.push_back(Arg1);
  Args.push_back(Arg2);

  if (Arg2->getType() == Type::getInt64Ty(Arg2->getContext())) {
    CallInst::Create(CopyMetadataFn, Args, "", CB);
  } else {
    //    CallInst::Create(CopyMetadataFn, args, "", call_inst);
  }
  Args.clear();

#if 0

  Value *Arg0Base = castToVoidPtr(getAssociatedBase(Arg0), CB);
  Value *Arg0Bound = castToVoidPtr(getAssociatedBound(Arg0), CB);
  Value *Arg1Base = castToVoidPtr(getAssociatedBase(Arg1), CB);
  Value *Arg1Bound = castToVoidPtr(getAssociatedBound(Arg1), CB);
  Args.push_back(Arg0);
  Args.push_back(Arg0Base);
  Args.push_back(Arg0Bound);
  Args.push_back(Arg1);
  Args.push_back(Arg1Base);
  Args.push_back(Arg1Bound);
  Args.push_back(Arg2);

  CallInst::Create(MemcpyDereferenceCheckFn, Args.begin(), Args.end(), "", CB);

#endif
  return;
}

void SoftBoundCETSPass::handleExtractElement(ExtractElementInst *EEI) {
  if (!isa<PointerType>(EEI->getType()))
    return;

  auto *VecOp = EEI->getOperand(0);

  auto *Idx = EEI->getOperand(1);

  if (ClSpatialSafety) {
    auto *VectorBases = getAssociatedBase(VecOp);
    auto *VectorBounds = getAssociatedBound(VecOp);

    Value *PtrBase = ExtractElementInst::Create(VectorBases, Idx, "", EEI);
    Value *PtrBound = ExtractElementInst::Create(VectorBounds, Idx, "", EEI);

    associateBaseBound(EEI, PtrBase, PtrBound);
  }

  if (ClTemporalSafety) {
    auto *VectorKeys = getAssociatedKey(VecOp);
    auto *VectorLocks = getAssociatedLock(VecOp);

    Value *PtrKey = ExtractElementInst::Create(VectorKeys, Idx, "", EEI);
    Value *PtrLock = ExtractElementInst::Create(VectorLocks, Idx, "", EEI);

    associateKeyLock(EEI, PtrKey, PtrLock);
  }
}

void SoftBoundCETSPass::handleInsertElement(InsertElementInst *IEI) {
  Value *VecOp = IEI->getOperand(0);
  Value *ValOp = IEI->getOperand(1);
  Value *Idx = IEI->getOperand(2);

  // check second operand is Pointer (implies first operand is vector of
  // pointers)
  if (!isa<PointerType>(ValOp->getType()))
    return;

  if (ClSpatialSafety) {

    // get metadata of pointer to be inserted into vector
    Value *Base = getAssociatedBase(ValOp);
    Value *Bound = getAssociatedBound(ValOp);
    // get metadata vectors of vector where pointer is inserted
    auto *VectorBases = getAssociatedBase(VecOp);
    auto *VectorBounds = getAssociatedBound(VecOp);
    // insert metadata of pointer into metadata vectors, update the metadata
    // vectors in the global table
    auto *NewBases = InsertElementInst::Create(VectorBases, Base, Idx, "", IEI);
    auto *NewBounds =
        InsertElementInst::Create(VectorBounds, Bound, Idx, "", IEI);
    associateBaseBound(IEI, NewBases, NewBounds);
  }

  if (ClTemporalSafety) {
    Value *Key = getAssociatedKey(ValOp);
    Value *Lock = getAssociatedLock(ValOp);
    auto *VectorKeys = getAssociatedKey(VecOp);
    auto *VectorLocks = getAssociatedLock(VecOp);
    auto *NewKeys = InsertElementInst::Create(VectorKeys, Key, Idx, "", IEI);
    auto *NewLocks = InsertElementInst::Create(VectorLocks, Lock, Idx, "", IEI);

    associateKeyLock(IEI, NewKeys, NewLocks);
  }
}

void SoftBoundCETSPass::handleInsertValue(InsertValueInst *IVI) {

  if (!isTypeWithPointers(IVI->getType()))
    return;

  Value *AggOp = IVI->getAggregateOperand();
  Value *ValOp = IVI->getInsertedValueOperand();

  if (!isTypeWithPointers(ValOp->getType())) {
    propagateMetadata(AggOp, IVI);
    return;
  }

  size_t Idx = flattenAggregateIndices(AggOp->getType(), IVI->getIndices());

  if (ClSpatialSafety) {
    TinyPtrVector<Value *> AggregateBases, AggregateBounds;
    AggregateBases = TinyPtrVector<Value *>(getAssociatedBases(AggOp));
    AggregateBounds = TinyPtrVector<Value *>(getAssociatedBounds(AggOp));

    auto Bases = getAssociatedBases(ValOp);
    auto Bounds = getAssociatedBounds(ValOp);
    for (unsigned J = 0; J < Bases.size(); ++J) {

      static_cast<MutableArrayRef<Value *>>(AggregateBases)[Idx + J] = Bases[J];
      static_cast<MutableArrayRef<Value *>>(AggregateBounds)[Idx + J] =
          Bounds[J];
    }

    associateAggregateBaseBound(IVI, AggregateBases, AggregateBounds);
  }

  if (ClTemporalSafety) {
    TinyPtrVector<Value *> AggregateKeys, AggregateLocks;
    AggregateKeys = TinyPtrVector<Value *>(getAssociatedKeys(AggOp));
    AggregateLocks = TinyPtrVector<Value *>(getAssociatedLocks(AggOp));
    auto Keys = getAssociatedKeys(ValOp);
    auto Locks = getAssociatedLocks(ValOp);
    for (unsigned J = 0; J < Keys.size(); ++J) {
      static_cast<MutableArrayRef<Value *>>(AggregateKeys)[Idx + J] = Keys[J];
      static_cast<MutableArrayRef<Value *>>(AggregateLocks)[Idx + J] = Locks[J];
    }

    associateAggregateKeyLock(IVI, AggregateKeys, AggregateLocks);
  }
}

void SoftBoundCETSPass::handleExtractValue(ExtractValueInst *EVI) {
  Type *EVITy = EVI->getType();

  if (!isTypeWithPointers(EVITy)) {
    return;
  }
  Value *AggOp = EVI->getAggregateOperand();

  size_t StartIdx =
      flattenAggregateIndices(AggOp->getType(), EVI->getIndices());
  size_t MetadataCount = countMetadata(EVITy);

  if (ClSpatialSafety) {

    TinyPtrVector<Value *> Bases, Bounds;
    auto AggregateBases = getAssociatedBases(AggOp);
    auto AggregateBounds = getAssociatedBounds(AggOp);
    for (size_t J = StartIdx; J < StartIdx + MetadataCount; ++J) {
      Value *Base = AggregateBases[J];
      Value *Bound = AggregateBounds[J];
      Bases.push_back(Base);
      Bounds.push_back(Bound);
    }

    associateAggregateBaseBound(EVI, Bases, Bounds);
  }

  if (ClTemporalSafety) {
    TinyPtrVector<Value *> Keys, Locks;
    auto AggregateKeys = getAssociatedKeys(AggOp);
    auto AggregateLocks = getAssociatedLocks(AggOp);
    for (size_t J = StartIdx; J < StartIdx + MetadataCount; ++J) {
      Value *Key = AggregateKeys[J];
      Value *Lock = AggregateLocks[J];
      Keys.push_back(Key);
      Locks.push_back(Lock);
    }
    associateAggregateKeyLock(EVI, Keys, Locks);
  }
}

void SoftBoundCETSPass::handleCall(CallBase *CallInst) {

  auto *ReturnTy = CallInst->getType();

  if (auto *F = CallInst->getCalledFunction()) {

    auto FName = F->getName();

    // handle calls to external (maybe uninstrumented) functions
    if (F->isDeclaration() &&
        !isExternalDefinitelyInstrumentedFunction(FName) &&
        !ClExternalLibsAreInstrumented) {
      if (isTypeWithPointers(ReturnTy)) {
        LLVM_DEBUG(
            dbgs() << "Handling call to external uninstrumented function: "
                   << FName << "\n");
        if (ClMaximalCompatibilityWithExternalLibs) {
          associateOmnivalidMetadata(CallInst);
        } else {
          associateInvalidMetadata(CallInst);
        }
      }
      return;
    }

    if (((FName.find("llvm.memcpy") == 0) ||
         (FName.find("llvm.memmove") == 0))) {
      addMemcopyMemsetCheck(CallInst, F);
      handleMemcpy(CallInst);
      return;
    }

    if (FName.find("llvm.memset") == 0) {
      addMemcopyMemsetCheck(CallInst, F);
      return;
    }

    if (FName.find("llvm.masked.load") == 0) {
      if (isTypeWithPointers(CallInst->getType()))
        handleMaskedVectorLoad(CallInst);
      return;
    }

    if (FName.find("llvm.stacksave") == 0) {
      associateOmnivalidMetadata(CallInst);
      return;
    }

    if (isIgnorableLLVMIntrinsic(FName))
      return;

    if (isFunctionNotToInstrument(FName)) {
      if (getNumPointerArgs(CallInst) > 0) {
        LLVM_DEBUG(
            dbgs() << "call to function where "
                      "isFunctionNotToInstrument=true with pointers in args:\n"
                   << FName << "\n");
      }
      if (isTypeWithPointers(ReturnTy)) {
        LLVM_DEBUG(
            dbgs()
            << "call to function where "
               "isFunctionNotToInstrument=true with pointer(s) returned:\n"
            << FName << "\n");
        if (ClAssociateMissingMetadata) {
          if (ClAssociateOmnivalidMetadataWhenMissing)
            associateOmnivalidMetadata(CallInst);
          else
            associateInvalidMetadata(CallInst);
        } else
          assert(0 && "Should not return pointer");
      }
      return;
    }
  }

  if (isa<InlineAsm>(CallInst->getCalledOperand())) {

    if (!isTypeWithPointers(ReturnTy)) {
      return;
    }
    LLVM_DEBUG(errs() << "Pointer from inline assembly: " << *CallInst << '\n');

    associateOmnivalidMetadata(CallInst);
    return;
  }

  Instruction *InsertAt;
  switch (CallInst->getOpcode()) {
  case Instruction::Call: {
    InsertAt = getNextInstruction(CallInst);
    break;
  }
  case Instruction::Invoke: {
    InvokeInst *Invoke = dyn_cast<InvokeInst>(CallInst);
    BasicBlock *NormalBlock = Invoke->getNormalDest();

    // normal_block might have preds besides the current one
    // to guarantee that dealloc is only called after an alloc,
    // create a new bb jumping to the original bb after dealloc
    BasicBlock *DeallocBlock = BasicBlock::Create(
        NormalBlock->getContext(), "", NormalBlock->getParent(), NormalBlock);
    BranchInst::Create(NormalBlock, DeallocBlock);
    Invoke->setNormalDest(DeallocBlock);
    InsertAt = &*DeallocBlock->getFirstInsertionPt();
    for (PHINode &Phi : NormalBlock->phis()) {
      int Idx = Phi.getBasicBlockIndex(Invoke->getParent());
      if (Idx == -1)
        continue;
      Phi.setIncomingBlock(Idx, DeallocBlock);
    }

    break;
  }
  default: {
    llvm_unreachable("instruction must be call or invoke!");
    break;
  }
  }

  //  call_inst->setCallingConv(CallingConv::C);

  // Count the number of pointer arguments and whether a pointer return
  size_t NumPointerArgs = getNumPointerArgs(CallInst);
  size_t NumPointerRets = countPointersInType(ReturnTy);

  if (NumPointerArgs || NumPointerRets) {
    introduceShadowStackAllocation(CallInst, NumPointerArgs + NumPointerRets);
  }

  if (NumPointerArgs) {
    size_t PointerArgNo = NumPointerRets;

    for (Use &Arg : CallInst->args()) {
      if (isTypeWithPointers(Arg->getType())) {
        PointerArgNo += introduceShadowStackStores(Arg, CallInst, PointerArgNo);
      }
    }
  }

  if (NumPointerRets) {
    // Shadow stack slots for return values start at index 0.
    introduceShadowStackLoads(CallInst, InsertAt, 0);
  }

  if (NumPointerArgs || NumPointerRets) {
    introduceShadowStackDeallocation(CallInst, InsertAt);
  }
}

void SoftBoundCETSPass::handleIntToPtr(IntToPtrInst *inttoptrinst) {
  Value *I = inttoptrinst;

  if (ClSpatialSafety) {
    if (ClAssociateIntToPtrCastsWithOmnivalidMetadata)
      associateBaseBound(I, MVoidNullPtr, MInfiniteBoundPtr);
    else
      associateBaseBound(I, MVoidNullPtr, MVoidNullPtr);
  }

  if (ClTemporalSafety) {
    if (ClAssociateIntToPtrCastsWithOmnivalidMetadata)
      associateKeyLock(I, MConstantIntOne, MGlobalLockOne);
    else
      associateKeyLock(I, MConstantIntZero, MGlobalLockOne);
  }
}

void SoftBoundCETSPass::gatherBaseBoundPass2(Function &F) {

  std::set<BasicBlock *> BBVisited;
  std::queue<BasicBlock *> BBWorklist;

  auto *BB = &F.getEntryBlock();
  BBWorklist.push(BB);

  while (BBWorklist.size() != 0) {

    BB = BBWorklist.front();

    BBWorklist.pop();
    if (BBVisited.count(BB)) {
      /* Block already visited */
      continue;
    }
    BBVisited.insert(BB);
    for (auto SI = succ_begin(BB), SE = succ_end(BB); SI != SE; ++SI) {
      BasicBlock *NextBB = *SI;
      BBWorklist.push(NextBB);
    }

    for (auto &I : *BB) {

      // If the instruction is not present in the original, no instrumentaion
      if (!MPresentInOriginal.count(&I))
        continue;

      switch (I.getOpcode()) {

      case Instruction::Store: {
        auto *Store = dyn_cast<StoreInst>(&I);
        assert(Store && "Not a Store instruction?");
        handleStore(Store);
      } break;

      case Instruction::PHI: {
        auto *PHI = dyn_cast<PHINode>(&I);
        assert(PHI && "Not a PHINode?");
        handlePHIPass2(PHI);
      } break;

      // TODO: is this necessary? already handled in first pass
      case BitCastInst::BitCast: {
        auto *BC = dyn_cast<BitCastInst>(&I);
        assert(BC && "Not a bitcast instruction?");
        if (isTypeWithPointers(BC->getType())) {
          handleBitCast(BC);
        }
      } break;

      default:
        break;
      } /* Switch Ends */
    }   /* BasicBlock iterator Ends */
  }     /* Function iterator Ends */
}

void SoftBoundCETSPass::introspectMetadata(Function *func, Value *ptr_value,
                                           Instruction *insert_at, int arg_no) {
  if (func->getName() != "debug_instrument_softboundcets")
    return;

  Value *ptr_base = getAssociatedBase(ptr_value);
  Value *ptr_bound = getAssociatedBound(ptr_value);

  Value *ptr_value_cast = castToVoidPtr(ptr_value, insert_at);
  Value *ptr_base_cast = castToVoidPtr(ptr_base, insert_at);
  Value *ptr_bound_cast = castToVoidPtr(ptr_bound, insert_at);

  Value *argno_value;

  argno_value = ConstantInt::get(
      Type::getInt32Ty(ptr_value->getType()->getContext()), arg_no, false);

  SmallVector<Value *, 8> args;

  args.push_back(ptr_value_cast);
  args.push_back(ptr_base_cast);
  args.push_back(ptr_bound_cast);
  args.push_back(argno_value);

  CallInst::Create(IntrospectMetadataFn, args, "", insert_at);
}

void SoftBoundCETSPass::freeFunctionKeyLock(Function *func, Value *&func_key,
                                            Value *&func_lock,
                                            Value *&func_xmm_key_lock) {
  if (func_key == NULL && func_lock == NULL) {
    return;
  }

  if ((func_key == NULL && func_lock != NULL) &&
      (func_key != NULL && func_lock == NULL)) {
    assert(0 && "inconsistent key lock");
  }

  Instruction *next_inst = NULL;

  for (Function::iterator b = func->begin(), be = func->end(); b != be; ++b) {

    BasicBlock *bb = dyn_cast<BasicBlock>(b);
    assert(bb && "basic block does not exist?");

    for (BasicBlock::iterator i = bb->begin(), ie = bb->end(); i != ie; ++i) {

      next_inst = dyn_cast<Instruction>(i);

      if (!isa<ReturnInst>(next_inst))
        continue;

      ReturnInst *ret = dyn_cast<ReturnInst>(next_inst);
      /* Insert a call to deallocate key and lock*/
      SmallVector<Value *, 8> args;
      Instruction *first_inst_func =
          dyn_cast<Instruction>(func->begin()->getFirstNonPHI());
      assert(first_inst_func && "function doesn't have any instruction ??");
      args.push_back(func_key);
      CallInst::Create(DeallocateStackLockAndKeyFn, args, "", ret);
    }
  }
}

void SoftBoundCETSPass::gatherBaseBoundPass1(Function &F) {
  // Scan over the pointer arguments and introduce metadata loads from the
  // shadow stack.
  int ArgCount = countPointersInType(F.getReturnType());

  for (auto &Arg : F.args()) {

    auto *ArgTy = Arg.getType();

    if (!isTypeWithPointers(ArgTy)) {
      continue;
    }

    Instruction *InsertAt = F.begin()->getFirstNonPHI();

    if (Arg.hasByValAttr()) {
      LLVM_DEBUG(dbgs() << "ByVal Attribute: " << Arg << "\n");
      LLVM_DEBUG(
          errs() << "Ensure FixByValAttributes Pass runs before "
                    "SoftBoundCETS! Please note the FixByValAttributes Pass "
                    "can right now only run in LTO on one single module.\n");
      assert(0 && "Pointer argument has byval attributes and the underlying"
                  "structure returns pointers");
    } else {
      ArgCount += introduceShadowStackLoads(&Arg, InsertAt, ArgCount);
    }
  }

  // Get lock and key for the function.
  Value *Key = NULL;
  Value *Lock = NULL;
  Value *func_xmm_key_lock = NULL;
  getFunctionKeyLock(&F, Key, Lock, func_xmm_key_lock);
  MFaultingBlock[&F] = createFaultBlock(&F);

#if 0
  if(ClTemporalSafety){
    if(Key == NULL || Lock == NULL){
      assert(0 && "function key lock null for the function");
    }
  }
#endif

  std::set<BasicBlock *> BBVisited;
  std::queue<BasicBlock *> BBWorklist;

  auto *BB = &F.getEntryBlock();
  BBWorklist.push(BB);

  while (BBWorklist.size() != 0) {

    BB = BBWorklist.front();

    BBWorklist.pop();
    if (BBVisited.count(BB)) {
      /* Block already visited */
      continue;
    }
    BBVisited.insert(BB);
    for (auto SI = succ_begin(BB), SE = succ_end(BB); SI != SE; ++SI) {
      BasicBlock *NextBB = *SI;
      BBWorklist.push(NextBB);
    }

    // Scan over the instructions and gather metadata.
    for (auto &I : *BB) {

      if (!MPresentInOriginal.count(&I))
        continue;

      // TODO: use llvm instruction visitor class
      switch (I.getOpcode()) {

      case Instruction::Alloca: {
        auto *AI = dyn_cast<AllocaInst>(&I);
        assert(AI && "Not an Alloca inst?");
        handleAlloca(AI, Key, Lock, func_xmm_key_lock);
      } break;

      case Instruction::Load: {
        auto *LI = dyn_cast<LoadInst>(&I);
        assert(LI && "Not a Load inst?");
        handleLoad(LI);
      } break;

      case Instruction::GetElementPtr: {
        auto *GEP = dyn_cast<GetElementPtrInst>(&I);
        assert(GEP && "Not a GEP inst?");
        handleGEP(GEP);
      } break;

      case BitCastInst::BitCast: {
        auto *BC = dyn_cast<BitCastInst>(&I);
        assert(BC && "Not a BitCast inst?");
        if (isTypeWithPointers(BC->getType())) {
          handleBitCast(BC);
        }
      } break;

      case Instruction::PHI: {
        auto *PHI = dyn_cast<PHINode>(&I);
        assert(PHI && "Not a phi node?");
        // printInstructionMap(&I);
        handlePHIPass1(PHI);
      } break;

      case Instruction::Call: {
        auto *CI = dyn_cast<CallInst>(&I);
        assert(CI && "Not a Call inst?");
        handleCall(CI);
      } break;

      case Instruction::Select: {
        auto *SI = dyn_cast<SelectInst>(&I);
        assert(SI && "Not a select inst?");
        handleSelect(SI);
      } break;

      case Instruction::Store: {
        break;
      }

      case Instruction::IntToPtr: {
        auto *IPI = dyn_cast<IntToPtrInst>(&I);
        assert(IPI && "Not a IntToPtrInst?");
        handleIntToPtr(IPI);
        break;
      }

      case Instruction::Ret: {
        auto *RI = dyn_cast<ReturnInst>(&I);
        assert(RI && "not a return inst?");
        handleReturnInst(RI);
      } break;

      case Instruction::ExtractElement: {
        auto *EEI = dyn_cast<ExtractElementInst>(&I);
        assert(EEI && "ExtractElementInst inst?");
        handleExtractElement(EEI);
      } break;

      case Instruction::InsertElement: {
        auto *IEI = dyn_cast<InsertElementInst>(&I);
        assert(IEI && "ExtractElementInst inst?");
        handleInsertElement(IEI);
      } break;

      case Instruction::ExtractValue: {
        auto *EVI = dyn_cast<ExtractValueInst>(&I);
        assert(EVI && "handle extract value inst?");
        handleExtractValue(EVI);
      } break;

      case Instruction::InsertValue: {
        auto *IVI = dyn_cast<InsertValueInst>(&I);
        handleInsertValue(IVI);
      } break;

      case Instruction::Invoke: {
        auto *II = dyn_cast<InvokeInst>(&I);
        handleCall(II);
      } break;
        // TODO[orthen]: consider if metadata about exception object can be
        // refined https://llvm.org/docs/LangRef.html#i-landingpad
        // https://llvm.org/devmtg/2011-09-16/EuroLLVM2011-ExceptionHandling.pdf
      case Instruction::LandingPad: {
        auto *LP = dyn_cast<LandingPadInst>(&I);
        associateOmnivalidMetadata(LP);
      } break;

      case Instruction::ShuffleVector: {
        auto *SV = dyn_cast<ShuffleVectorInst>(&I);
        if (isTypeWithPointers(SV->getType()))
          handleShuffleVector(SV);
      } break;

      default: {
        if (isTypeWithPointers(I.getType())) {
          LLVM_DEBUG(errs() << "Unhandled instruction: " << I << "\n");
          if (ClAssociateMissingMetadata)
            if (ClAssociateOmnivalidMetadataWhenMissing)
              associateOmnivalidMetadata(&I);
            else
              associateInvalidMetadata(&I);
          else
            assert(0 && "Instruction generating Pointer is not handled");
        }
      } break;
      }
    } // End instruction iteration.
  }   // End basic block iteration.

  if (ClTemporalSafety) {
    freeFunctionKeyLock(&F, Key, Lock, func_xmm_key_lock);
  }
}

void SoftBoundCETSPass::insertPointerMetadataLoad(
    Value *LoadSrc, SoftBoundCETSMetadata &Metadata, Instruction *InsertAt) {

  SmallVector<Value *, 8> Args;
  IRBuilder<> IRB(InsertAt);

  /* If the load returns a pointer, then load the base and bound
   * from the shadow space
   */
  Value *LoadSrcBitcast = castToVoidPtr(LoadSrc, InsertAt);
  /* address of pointer being pushed */

  Args.push_back(LoadSrcBitcast);

  if (ClSimpleMetadataMode) {
    if (ClSpatialSafety) {
      Metadata.Base = IRB.CreateCall(LoadMetadataBaseFn, Args, "");
      Metadata.Bound = IRB.CreateCall(LoadMetadataBoundFn, Args, "");
    }

    if (ClTemporalSafety) {
      Metadata.Lock = IRB.CreateCall(LoadMetadataLockFn, Args, "");
      Metadata.Key = IRB.CreateCall(LoadMetadataKeyFn, Args, "");
    }

  } else {
    auto *MetadataPtr = IRB.CreateCall(LoadMetadataPtrFn, {LoadSrcBitcast});

    unsigned KeyIdx = 0;
    unsigned LockIdx = 1;

    if (ClSpatialSafety) {
      auto *BasePtr = IRB.CreateStructGEP(MetadataPtr, 0, "baseptr");
      Metadata.Base = IRB.CreateLoad(BasePtr, "base");
      auto *BoundPtr = IRB.CreateStructGEP(MetadataPtr, 1, "boundptr");
      Metadata.Bound = IRB.CreateLoad(BoundPtr, "bound");

      KeyIdx = 2;
      LockIdx = 3;
    }
    if (ClTemporalSafety) {
      auto *KeyPtr = IRB.CreateStructGEP(MetadataPtr, KeyIdx, "keyptr");
      Metadata.Key = IRB.CreateLoad(KeyPtr, "key");
      auto *LockPtr = IRB.CreateStructGEP(MetadataPtr, LockIdx, "lockptr");
      Metadata.Lock = IRB.CreateLoad(LockPtr, "lock");
    }
  }
}

void SoftBoundCETSPass::insertVectorMetadataLoad(
    Value *LoadSrc, SoftBoundCETSMetadata &Metadata, Instruction *InsertAt,
    size_t NumElements) {

  IRBuilder<> IRB(InsertAt);
  Value *PointerOpBitcast = castToVoidPtr(LoadSrc, InsertAt);
  SmallVector<Value *, 8> Bases;
  SmallVector<Value *, 8> Bounds;
  SmallVector<Value *, 8> Keys;
  SmallVector<Value *, 8> Locks;

  for (uint64_t Idx = 0; Idx < NumElements; Idx++) {

    SmallVector<Value *, 8> Args;
    Args.push_back(PointerOpBitcast);
    Constant *IdxArg = ConstantInt::get(Type::getInt32Ty(*C), Idx);
    Args.push_back(IdxArg);

    if (ClSimpleMetadataMode) {
      if (ClSpatialSafety) {
        Value *Base =
            CallInst::Create(LoadVectorMetadataBaseFn, Args, "", InsertAt);
        Value *Bound =
            CallInst::Create(LoadVectorMetadataBoundFn, Args, "", InsertAt);
        Bases.push_back(Base);
        Bounds.push_back(Bound);
      }

      if (ClTemporalSafety) {
        Value *Lock =
            CallInst::Create(LoadVectorMetadataLockFn, Args, "", InsertAt);
        Value *Key =
            CallInst::Create(LoadVectorMetadataKeyFn, Args, "", InsertAt);
        Keys.push_back(Key);
        Locks.push_back(Lock);
      }

    } else {

      auto *MetadataPtr = IRB.CreateCall(LoadVectorMetadataPtrFn, Args);

      unsigned KeyIdx = 0;
      unsigned LockIdx = 1;

      if (ClSpatialSafety) {
        auto *BasePtr = IRB.CreateStructGEP(MetadataPtr, 0, "baseptr");
        Value *Base = IRB.CreateLoad(BasePtr, "base");
        Bases.push_back(Base);
        auto *BoundPtr = IRB.CreateStructGEP(MetadataPtr, 1, "boundptr");
        Value *Bound = IRB.CreateLoad(BoundPtr, "bound");
        Bounds.push_back(Bound);

        KeyIdx = 2;
        LockIdx = 3;
      }
      if (ClTemporalSafety) {
        auto *KeyPtr = IRB.CreateStructGEP(MetadataPtr, KeyIdx, "keyptr");
        Value *Key = IRB.CreateLoad(KeyPtr, "key");
        Keys.push_back(Key);
        auto *LockPtr = IRB.CreateStructGEP(MetadataPtr, LockIdx, "lockptr");
        Value *Lock = IRB.CreateLoad(LockPtr, "lock");
        Locks.push_back(Lock);
      }
    }
  }
  if (ClSpatialSafety) {
    Metadata.Base = createMetadataVector(Bases, InsertAt);
    Metadata.Bound = createMetadataVector(Bounds, InsertAt);
  }
  if (ClTemporalSafety) {
    Metadata.Key = createMetadataVector(Keys, InsertAt);
    Metadata.Lock = createMetadataVector(Locks, InsertAt);
  }
}

void SoftBoundCETSPass::handlePointerLoad(LoadInst *Load) {
  if (checkMetadataPresent(Load))
    return;
  SoftBoundCETSMetadata Metadata;
  insertPointerMetadataLoad(Load->getPointerOperand(), Metadata, Load);
  associateMetadata(Load, Metadata);
}

void SoftBoundCETSPass::handleAggregateLoad(LoadInst *Load) {
  /** (ds)
   * Ideally, this would work conversely to storing aggregates.
   * So first create allocas for every contained pointer.
   * Then generate GEPs and finally calls to the runtime.
   */

  Value *LoadSrc = Load->getPointerOperand();
  Type *LoadTy = Load->getType();
  Instruction *InsertAt = getNextInstruction(Load);
  // generate GEPs for each contained pointer
  SmallVector<Value *, 8> GEPs;
  generateAggregateGEPs(LoadSrc, LoadTy, InsertAt, GEPs);

  TinyPtrVector<Value *> Bases, Bounds, Keys, Locks;

  for (unsigned J = 0; J < GEPs.size(); ++J) {
    SoftBoundCETSMetadata Metadata;

    auto *GEP = GEPs[J];
    auto *GEPElementTy = cast<PointerType>(GEP->getType())->getElementType();
    assert(GEPElementTy->isPtrOrPtrVectorTy() &&
           "Loading aggregate member metadata for value which is neither a "
           "Pointer nor a Vector of Pointers");
    if (auto *VectorTy = dyn_cast<VectorType>(GEPElementTy)) {
      insertVectorMetadataLoad(GEP, Metadata, InsertAt,
                               VectorTy->getElementCount().getValue());
    } else {
      insertPointerMetadataLoad(GEP, Metadata, InsertAt);
    }

    if (ClSpatialSafety) {
      Bases.push_back(Metadata.Base);
      Bounds.push_back(Metadata.Bound);
    }
    if (ClTemporalSafety) {
      Keys.push_back(Metadata.Key);
      Locks.push_back(Metadata.Lock);
    }
  }

  if (ClSpatialSafety) {
    assert(Bases.size() == GEPs.size() && Bounds.size() == GEPs.size() &&
           "The number of metadata entries must match the number of generated "
           "GEPs");
  }
  if (ClTemporalSafety) {
    assert(Keys.size() == GEPs.size() && Locks.size() == GEPs.size() &&
           "The number of metadata entries must match the number of generated "
           "GEPs");
  }

  associateAggregateMetadata(Load, Bases, Bounds, Keys, Locks);
}

/* handleLoad Takes a load_inst If the load is through a pointer
 * which is a global then inserts base and bound for that global
 * Also if the loaded value is a pointer then loads the base and
 * bound for for the pointer from the shadow space
 */

void SoftBoundCETSPass::handleLoad(LoadInst *Load) {
  Type *LoadTy = Load->getType();
  if (!isTypeWithPointers(LoadTy)) {
    return;
  }
  GetElementPtrInst *GepInst =
      dyn_cast<GetElementPtrInst>(Load->getPointerOperand());

  if (GepInst && isVaargGep(GepInst)) {
    associateOmnivalidMetadata(Load);
    if (ClAssociateVaargPointerWithOmnivalidMetadata)
      varargAssociatePointerLoads(Load);
  } else if (isVectorWithPointers(LoadTy)) {
    handleVectorLoad(Load);
  } else if (isa<PointerType>(LoadTy)) {
    handlePointerLoad(Load);
  } else if (LoadTy->isAggregateType()) {
    handleAggregateLoad(Load);
  } else {
    assert(0 && "Loading type which contains pointers but is not handled");
  }
}

// A definition of a global with an initializer is semantically similar
// to a store of a constant value to the address of the global.
// Thus we gather metadata for all pointers in the initializer and generate
// metadata_store calls, just like we do for actual store instructions.
// The calls will be inserted into the special __softboundcets_globals_ctor
// function, which is called during program initialization.
void SoftBoundCETSPass::addMetadataToGlobals(Module &M) {

  for (auto &GV : M.globals()) {
    if (GV.getSection() == "llvm.metadata" ||
        GV.getName() == "llvm.global_ctors" ||
        GV.getName() == "llvm.global_dtors" ||
        GV.getName().contains("softboundcets"))
      continue;

    LLVM_DEBUG(dbgs() << "Associating global with metadata: " << GV << "\n");
    addMetadataToGlobal(GV);
  }
}

inline void SoftBoundCETSPass::addMetadataToGlobal(GlobalVariable &GV) {

  TinyPtrVector<Value *> Bases, Bounds, Keys;

  if (ClSpatialSafety) {
    Bases = createConstantBases<Value>(dyn_cast<Constant>(&GV));
    Bounds = createConstantBounds<Value>(dyn_cast<Constant>(&GV), true);
    associateAggregateBase(&GV, Bases);
    associateAggregateBound(&GV, Bounds);
  }

  if (ClTemporalSafety) {
    Keys = createConstantKeys<Value>(dyn_cast<Constant>(&GV), true);
    auto Locks = createDummyMetadata<Value>(GV.getType(), MGlobalLockOne);
    associateAggregateKeyLock(&GV, Keys, Locks);
  }

  auto *GVValTy = GV.getValueType();
  if (!isTypeWithPointers(GVValTy))
    return;

  Instruction *InsertAt = getGlobalsInitializerInsertPoint(*M);
  SmallVector<Value *, 8> GEPs;
  generateAggregateGEPs(&GV, GVValTy, InsertAt, GEPs);

  if (GV.hasInitializer()) {
    Constant *GVInitializer = GV.getInitializer();
    LLVM_DEBUG(dbgs() << "Global Initializer: " << *GVInitializer << "\n");
    if (ClSpatialSafety) {
      Bases = createConstantBases<Value>(dyn_cast<Constant>(GVInitializer));
      Bounds =
          createConstantBounds<Value>(dyn_cast<Constant>(GVInitializer), true);
    }
    if (ClTemporalSafety) {
      Keys = createConstantKeys<Value>(dyn_cast<Constant>(GVInitializer), true);
    }
  } else {
    if (ClSpatialSafety) {
      Bases = createDummyMetadata<Value>(GVValTy, MVoidNullPtr);
      if (ClAssociateZeroInitializedGlobalsWithOmnivalidMetadata) {
        Bounds = createDummyMetadata<Value>(GVValTy, MInfiniteBoundPtr);
      } else {
        Bounds = createDummyMetadata<Value>(GVValTy, MVoidNullPtr);
      }
    }
    if (ClTemporalSafety) {
      if (ClAssociateZeroInitializedGlobalsWithOmnivalidMetadata) {
        Keys = createDummyMetadata<Value>(GVValTy, MConstantIntOne);
      } else {
        Keys = createDummyMetadata<Value>(GVValTy, MConstantIntZero);
      }
    }
  }

  for (unsigned Idx = 0; Idx < GEPs.size(); ++Idx) {
    Value *Base = NULL;
    Value *Bound = NULL;
    Value *Key = NULL;

    if (ClSpatialSafety) {
      Base = Bases[Idx];
      Bound = Bounds[Idx];
    }
    if (ClTemporalSafety) {
      Key = Keys[Idx];
    }

    insertPointerMetadataStore(GEPs[Idx], Base, Bound, Key, MGlobalLockOne,
                               InsertAt);
  }
}

// get the index into the compile-time metadata vector of an aggregate structure
size_t SoftBoundCETSPass::flattenAggregateIndices(Type *Ty,
                                                  ArrayRef<unsigned> Indices) {
  switch (Ty->getTypeID()) {
  case Type::PointerTyID: {
    assert(Indices.empty() && "Too many indices for aggregate type!");
    return 0;
  }

  case Type::StructTyID: {
    assert(!Indices.empty() && "Too few indices for aggregate type!");
    ArrayRef<Type *> Subtypes = Ty->subtypes();
    assert(Indices[0] < Subtypes.size() && "Aggregate index out of bounds!");

    size_t Sum = 0;
    for (unsigned J = 0; J < Indices[0]; ++J) {
      Sum += countMetadata(Subtypes[J]);
    }
    Sum += flattenAggregateIndices(Subtypes[Indices[0]], Indices.drop_front(1));
    return Sum;
  }

  case Type::ArrayTyID: {
    assert(!Indices.empty() && "Too few indices for aggregate type!");
    ArrayType *ArrayTy = cast<ArrayType>(Ty);
    assert(Indices[0] < ArrayTy->getNumElements() &&
           "Aggregate index out of bounds!");
    Type *ElTy = ArrayTy->getElementType();

    return Indices[0] * countMetadata(ElTy) +
           flattenAggregateIndices(ElTy, Indices.drop_front(1));
  }

  case Type::FixedVectorTyID: {
    if (isVectorWithPointers(Ty)) {
      return 0;
    }
    break;
  }
  default: {
    assert(Indices.empty() && "Too many indices for aggregate type!");
    return 0;
  }
  }
  return 0;
}

/** (ds)
 * Traverses an aggregate type (`pointee_type`) recursively to find nested
 * pointer types. For each contained pointer type, a GEP value is generated
 * using the base (`pointer`). Returns a list of pointer values in the range
 * GEP(pointer, 0) to GEP(pointer, 1). For example the pointee type {{i64, ptr},
 * [2 x ptr]} and pointer p would result in [GEP(p, 0, 0, 1), GEP(p, 0, 1, 0),
 * GEP(p, 0, 1, 1)]
 */
void SoftBoundCETSPass::generateAggregateGEPs(Value *Ptr, Type *PointeeTy,
                                              Instruction *InsertAt,
                                              SmallVector<Value *, 8> &GEPs) {
  // Inner visitor struct containing state.
  struct TypeVisitor {
    Value *Ptr;
    Type *PointeeTy;
    Instruction *InsertAt;
    // "path" to the current type, acts like a stack
    TinyPtrVector<Value *> &Indices;
    // already generated GEPs
    SmallVector<Value *, 8> &GEPs;

    void visit(Type *Ty) {
      switch (Ty->getTypeID()) {
      case Type::PointerTyID: {
        Value *GEP;
        // generate (constant) GEP using indices
        if (Constant *ConstPtr = dyn_cast<Constant>(Ptr)) {
          GEP = ConstantExpr::getGetElementPtr(PointeeTy, ConstPtr,
                                               ArrayRef<Value *>(Indices));
        } else {
          GEP = GetElementPtrInst::Create(PointeeTy, Ptr,
                                          ArrayRef<Value *>(Indices),
                                          Ptr->getName() + ".gep", InsertAt);
        }
        GEPs.push_back(GEP);
        break;
      }

      case Type::StructTyID: {
        ArrayRef<Type *> SubTypes = Ty->subtypes();
        // visit each subtype in struct
        for (unsigned J = 0; J < SubTypes.size(); ++J) {
          Indices.push_back(
              ConstantInt::get(Type::getInt32Ty(PointeeTy->getContext()), J));
          visit(SubTypes[J]);
          Indices.pop_back();
        }
        break;
      }

      case Type::ArrayTyID: {
        ArrayType *ArrayTy = cast<ArrayType>(Ty);
        Type *ElTy = ArrayTy->getElementType();
        // visit the array element type n times
        // this is rather inefficient for larger arrays as we duplicate work
        // a better solution would be to visit elt_type once and copy the
        // results
        for (unsigned J = 0; J < ArrayTy->getNumElements(); ++J) {
          Indices.push_back(
              ConstantInt::get(Type::getInt32Ty(PointeeTy->getContext()), J));
          visit(ElTy);
          Indices.pop_back();
        }
        break;
      }

      case Type::FixedVectorTyID: {
        FixedVectorType *FVTy = cast<FixedVectorType>(Ty);
        if (FVTy->getElementType()->isPointerTy()) {
          Value *GEP = GetElementPtrInst::Create(
              PointeeTy, Ptr, ArrayRef<Value *>(Indices),
              Ptr->getName() + ".gep", InsertAt);
          GEPs.push_back(GEP);
        }
        break;
      }

      default: {
      }
      }
    }
  };

  TinyPtrVector<Value *> Indices;
  Indices.push_back(
      ConstantInt::get(Type::getInt32Ty(PointeeTy->getContext()), 0));
  struct TypeVisitor Visitor = {Ptr, PointeeTy, InsertAt, Indices, GEPs};
  Visitor.visit(PointeeTy);
}

SmallVector<std::tuple<uint8_t, uint8_t>, 8>
SoftBoundCETSPass::getMetadataOrder(Type *Ty) {
  // Inner visitor struct containing state.
  struct TypeVisitor {
    SmallVector<std::tuple<uint8_t, uint8_t>, 8> &MetadataOrder;

    void visit(Type *Ty) {
      switch (Ty->getTypeID()) {
      case Type::PointerTyID: {
        MetadataOrder.push_back({0, 1});
        break;
      }

      case Type::StructTyID: {
        ArrayRef<Type *> SubTypes = Ty->subtypes();
        // visit each subtype in struct
        for (unsigned J = 0; J < SubTypes.size(); ++J) {
          visit(SubTypes[J]);
        }
        break;
      }

      case Type::ArrayTyID: {
        ArrayType *ArrayTy = cast<ArrayType>(Ty);
        Type *ElTy = ArrayTy->getElementType();
        // visit the array element type n times
        // this is rather inefficient for larger arrays as we duplicate work
        // a better solution would be to visit elt_type once and copy the
        // results
        for (unsigned J = 0; J < ArrayTy->getNumElements(); ++J) {
          visit(ElTy);
        }
        break;
      }

      case Type::FixedVectorTyID: {
        FixedVectorType *FVTy = cast<FixedVectorType>(Ty);
        if (FVTy->getElementType()->isPointerTy()) {
          MetadataOrder.push_back({1, FVTy->getNumElements()});
        }
        break;
      }

      default: {
      }
      }
    }
  };

  SmallVector<std::tuple<uint8_t, uint8_t>, 8> MetadataOrder;
  struct TypeVisitor Visitor = {MetadataOrder};
  Visitor.visit(Ty);
  return MetadataOrder;
}

template <typename T>
TinyPtrVector<T *> SoftBoundCETSPass::createDummyMetadata(Type *Ty,
                                                          Constant *Metadatum) {
  TinyPtrVector<T *> DummyMetadata;
  auto MetadataOrder = getMetadataOrder(Ty);

  for (auto &MetadataType : MetadataOrder) {
    if (std::get<0>(MetadataType) == 0) {
      DummyMetadata.push_back(Metadatum);
    } else if (std::get<0>(MetadataType) == 1) {
      auto VectorSize = std::get<1>(MetadataType);
      SmallVector<Constant *> MetadataArray(VectorSize, Metadatum);
      auto *MetadataVector = ConstantVector::get(MetadataArray);
      DummyMetadata.push_back(MetadataVector);
    }
  }
  return DummyMetadata;
}

TinyPtrVector<Value *> SoftBoundCETSPass::createDummyLocks(Type *Ty) {
  TinyPtrVector<Value *> DummyLocks;
  auto MetadataOrder = getMetadataOrder(Ty);

  for (auto &MetadataType : MetadataOrder) {
    if (std::get<0>(MetadataType) == 0) {
      auto *Lock = new GlobalVariable(
          *M, MConstantIntOne->getType(), false, GlobalValue::InternalLinkage,
          MConstantIntOne, "__softboundcets_omnivalid_lock1");
      DummyLocks.push_back(Lock);
      MGlobalLockOnes.insert(Lock);
    } else if (std::get<0>(MetadataType) == 1) {
      auto VectorSize = std::get<1>(MetadataType);
      SmallVector<Constant *> MetadataArray;
      for (size_t Idx = 0; Idx < VectorSize; Idx++) {
        Constant *Lock = new GlobalVariable(
            *M, MConstantIntOne->getType(), false, GlobalValue::InternalLinkage,
            MConstantIntOne, "__softboundcets_omnivalid_lock1");
        MGlobalLockOnes.insert(Lock);
        MetadataArray.push_back(Lock);
      }
      auto *MetadataVector = ConstantVector::get(MetadataArray);
      DummyLocks.push_back(MetadataVector);
    }
  }
  return DummyLocks;
}

void SoftBoundCETSPass::associateOmnivalidMetadata(Value *Val) {
  auto *ValTy = Val->getType();
  if (ClSpatialSafety) {
    auto Bases = createDummyMetadata<Value>(ValTy, MVoidNullPtr);
    auto Bounds = createDummyMetadata<Value>(ValTy, MInfiniteBoundPtr);
    associateAggregateBaseBound(Val, Bases, Bounds);
  }
  if (ClTemporalSafety) {
    auto Keys = createDummyMetadata<Value>(ValTy, MConstantIntOne);
    auto Locks = createDummyLocks(ValTy);
    associateAggregateKeyLock(Val, Keys, Locks);
  }
}

void SoftBoundCETSPass::associateInvalidMetadata(Value *Val) {
  auto *ValTy = Val->getType();
  if (ClSpatialSafety) {
    auto Bases = createDummyMetadata<Value>(ValTy, MVoidNullPtr);
    auto Bounds = createDummyMetadata<Value>(ValTy, MVoidNullPtr);
    associateAggregateBaseBound(Val, Bases, Bounds);
  }
  if (ClTemporalSafety) {
    auto Keys = createDummyMetadata<Value>(ValTy, MConstantIntZero);
    auto Locks = createDummyLocks(ValTy);
    associateAggregateKeyLock(Val, Keys, Locks);
  }
}

SmallVector<Value *>
SoftBoundCETSPass::unpackMetadataArray(ArrayRef<Value *> MetadataVals,
                                       Instruction *InsertAt) {
  SmallVector<Value *> UnpackedMetadata;
  for (auto *MetadataVal : MetadataVals) {
    switch (MetadataVal->getType()->getTypeID()) {
    case Type::FixedVectorTyID: {
      auto VectorMetadata = extractVectorValues(MetadataVal, InsertAt);
      UnpackedMetadata.append(VectorMetadata);
      break;
    }
    default:
      UnpackedMetadata.push_back(MetadataVal);
    }
  }
  return UnpackedMetadata;
}

TinyPtrVector<Value *>
SoftBoundCETSPass::packMetadataArray(ArrayRef<Value *> SingleMetadataVals,
                                     Type *Ty, Instruction *InsertAt) {
  TinyPtrVector<Value *> PackedMetadata;
  auto MetadataOrder = getMetadataOrder(Ty);
  size_t MetadataValsIdx = 0;

  for (auto &MetadataType : MetadataOrder) {
    if (std::get<0>(MetadataType) == 0) {
      auto *SingleMetadatum = SingleMetadataVals[MetadataValsIdx];
      PackedMetadata.push_back(SingleMetadatum);
      MetadataValsIdx++;
    } else if (std::get<0>(MetadataType) == 1) {
      auto VectorSize = std::get<1>(MetadataType);
      auto *MetadataVector = createMetadataVector(
          SingleMetadataVals.slice(MetadataValsIdx, VectorSize), InsertAt);
      PackedMetadata.push_back(MetadataVector);
      MetadataValsIdx += VectorSize;
    }
  }
  return PackedMetadata;
}

// NOTE: summary for constants
// just like getConstantExprBaseBound recursively
// 1. handle ConstantData
// a) ConstantPointerNull -> invalid metadata by createDummyMetadata
// b) Undef -> invalid metadata by createDummyMetadata if it contains pointers
// c) ConstantAggregateZero -> invalid metadata by createDummyMetadata if it
// contains pointers
// 2. handle ConstantAggregate
// a) ConstantArray -> call getConstantExprBaseBound on one element, push times
// Numelement on metadata array b) ConstantStruct -> call
// getConstantExprBaseBound on each subelement c) ConstantVector -> if it
// contains pointers, create metadata vector with invalid metadata
// 3. Globals
// a) Function -> create base=pointer, bound=pointer+DL.getPointerSize
// b) Global Variable -> get underlying type -> get typesizeinbits

template <typename T>
TinyPtrVector<T *> SoftBoundCETSPass::createConstantBases(Constant *Const) {
  TinyPtrVector<T *> Bases;

  if (MValueBaseMap.count(Const)) {
    auto ConstBases = MValueBaseMap[Const];
    for (auto *Base : ConstBases) {
      Bases.push_back(dyn_cast<Constant>(Base));
    }
    return Bases;
  }

  if (isa<ConstantPointerNull>(Const)) {
    Bases.push_back(MVoidNullPtr);
    return Bases;
  }
  if (isa<Function>(Const)) {
    auto *BaseCast = ConstantExpr::getBitCast(Const, MVoidPtrTy);
    Bases.push_back(BaseCast);
    return Bases;
  }
  if (auto *Global = dyn_cast<GlobalValue>(Const)) {
    auto *ConstCast = ConstantExpr::getBitCast(Const, MVoidPtrTy);
    Bases.push_back(ConstCast);
    return Bases;
  }
  if (auto *Undefined = dyn_cast<UndefValue>(Const)) {
    return createDummyMetadata<T>(Undefined->getType(), MVoidNullPtr);
  }
  if (auto *CAggZero = dyn_cast<ConstantAggregateZero>(Const)) {
    return createDummyMetadata<T>(CAggZero->getType(), MVoidNullPtr);
  }
  if (ConstantExpr *Expr = dyn_cast<ConstantExpr>(Const)) {

    // ignore all types that do not contain pointers
    if(!isTypeWithPointers(Expr->getType()))
      return Bases;


    switch (Expr->getOpcode()) {
    case Instruction::GetElementPtr: {
      Constant *Op = cast<Constant>(Expr->getOperand(0));
      return createConstantBases<T>(Op);
    }

    case BitCastInst::BitCast: {
      Constant *Op = cast<Constant>(Expr->getOperand(0));
      return createConstantBases<T>(Op);
    }

    case Instruction::IntToPtr: {
      LLVM_DEBUG(errs() << "Unhandled IntToPtr operation: " << *Const << '\n');
      Bases.push_back(MVoidNullPtr);
      return Bases;
    }

    case Instruction::ExtractElement: {
      auto *VBases = dyn_cast<Constant>(getAssociatedBase(Expr->getOperand(0)));
      auto *Idx = Expr->getOperand(1);
      auto *EBase = ConstantExpr::getExtractElement(VBases, Idx);
      Bases.push_back(EBase);
      return Bases;
    }

    case Instruction::InsertElement: {
      auto *VBases = dyn_cast<Constant>(getAssociatedBase(Expr->getOperand(0)));
      auto *ElementBase = Expr->getOperand(1);
      auto *Idx = Expr->getOperand(2);
      auto *NewBases = ConstantExpr::getInsertElement(VBases, ElementBase, Idx);
      Bases.push_back(NewBases);
      return Bases;
    }

    case Instruction::ExtractValue: {
      Value *AggOp = Expr->getOperand(0);
      auto VBases = getAssociatedBases(AggOp);

      size_t StartIdx =
        flattenAggregateIndices(AggOp->getType(), Expr->getIndices());
      size_t MetadataCount = countMetadata(Expr->getType());

      for (size_t J = StartIdx; J < StartIdx + MetadataCount; ++J) {
        Value *Base = VBases[J];
        Bases.push_back(dyn_cast<T>(Base));
      }

      return Bases;
    }

    case Instruction::InsertValue: {
      Constant *AggOp = Expr->getOperand(0);
      Constant *ValOp = Expr->getOperand(1);

      auto AggBases = getAssociatedBases(AggOp);
        for (auto *Base: AggBases) {
          Bases.push_back(dyn_cast<T>(Base));
        }

      if (!isTypeWithPointers(ValOp->getType()))
        return Bases;

      auto ValBases = getAssociatedBases(ValOp);
      size_t Idx = flattenAggregateIndices(AggOp->getType(), Expr->getIndices());

      for (unsigned J = 0; J < ValBases.size(); ++J) {
        static_cast<MutableArrayRef<T *>>(Bases)[Idx + J] = dyn_cast<T>(ValBases[J]);
      }

      return Bases;
    }
   }
  }
  if (auto *CAgg = dyn_cast<ConstantAggregate>(Const)) {
    if (auto *CArray = dyn_cast<ConstantArray>(CAgg)) {
      for (size_t i = 0; i < CArray->getType()->getNumElements(); i++) {
        auto CBases =
            createConstantBases<T>(CArray->getAggregateElement((unsigned)i));
        for (auto *Base : CBases) {
          Bases.push_back(Base);
        }
      }
      return Bases;
    }

    if (auto *CVector = dyn_cast<ConstantVector>(CAgg)) {
      auto *VectorTy = CVector->getType();
      if (isVectorWithPointers(VectorTy)) {
        TinyPtrVector<Constant *> VecBases;
        for (size_t i = 0; i < VectorTy->getNumElements(); i++) {
          auto ElBases =
              createConstantBases<Constant>(CVector->getAggregateElement(i));
          VecBases.push_back(ElBases.front());
        }
        auto *VecBase = ConstantVector::get(VecBases);
        Bases.push_back(VecBase);
      }
      return Bases;
    }

    if (auto *CStruct = dyn_cast<ConstantStruct>(CAgg)) {
      for (size_t i = 0; i < CStruct->getType()->getNumElements(); i++) {
        auto ElBases = createConstantBases<T>(CStruct->getAggregateElement(i));
        for (auto *Base : ElBases) {
          Bases.push_back(Base);
        }
      }
      return Bases;
    }
  }

  return Bases;
}

template <typename T>
TinyPtrVector<T *> SoftBoundCETSPass::createConstantBounds(Constant *Const,
                                                           bool isGlobal) {
  TinyPtrVector<T *> Bounds;

  if (MValueBoundMap.count(Const)) {
    auto ConstBounds = MValueBoundMap[Const];
    for (auto *Bound : ConstBounds) {
      Bounds.push_back(dyn_cast<Constant>(Bound));
    }
    return Bounds;
  }

  if (isa<ConstantPointerNull>(Const)) {
    if (isGlobal && ClAssociateZeroInitializedGlobalsWithOmnivalidMetadata)
      Bounds.push_back(MInfiniteBoundPtr);
    else
      Bounds.push_back(MVoidNullPtr);
    return Bounds;
  }
  if (isa<Function>(Const)) {
    auto *BoundCast = ConstantExpr::getBitCast(Const, MVoidPtrTy);
    Bounds.push_back(BoundCast);
    return Bounds;
  }
  if (auto *Global = dyn_cast<GlobalValue>(Const)) {
    Type *GlobalTy = Global->getValueType();

    Constant *GEPIdx =
        ConstantInt::get(Type::getInt32Ty(GlobalTy->getContext()), 1);
    Constant *Bound = ConstantExpr::getGetElementPtr(GlobalTy, Const, GEPIdx);
    auto *BoundCast = ConstantExpr::getBitCast(Bound, MVoidPtrTy);
    Bounds.push_back(BoundCast);
    return Bounds;
  }
  if (auto *Undefined = dyn_cast<UndefValue>(Const)) {
    if (isGlobal && ClAssociateZeroInitializedGlobalsWithOmnivalidMetadata)
      return createDummyMetadata<T>(Undefined->getType(), MInfiniteBoundPtr);
    return createDummyMetadata<T>(Undefined->getType(), MVoidNullPtr);
  }
  if (auto *CAggZero = dyn_cast<ConstantAggregateZero>(Const)) {
    if (isGlobal && ClAssociateZeroInitializedGlobalsWithOmnivalidMetadata)
      return createDummyMetadata<T>(CAggZero->getType(), MInfiniteBoundPtr);
    return createDummyMetadata<T>(CAggZero->getType(), MVoidNullPtr);
  }
  if (ConstantExpr *Expr = dyn_cast<ConstantExpr>(Const)) {

    // ignore all types that do not contain pointers
    if(!isTypeWithPointers(Expr->getType()))
      return Bounds;

    switch (Expr->getOpcode()) {
    case Instruction::GetElementPtr: {
      Constant *Op = cast<Constant>(Expr->getOperand(0));
      return createConstantBounds<T>(Op);
    }

    case BitCastInst::BitCast: {
      Constant *Op = cast<Constant>(Expr->getOperand(0));
      return createConstantBounds<T>(Op);
    }

    case Instruction::IntToPtr: {
      LLVM_DEBUG(errs() << "Unhandled IntToPtr operation: " << *Const << '\n');
      if (ClAssociateIntToPtrCastsWithOmnivalidMetadata)
        Bounds.push_back(MInfiniteBoundPtr);
      else
        Bounds.push_back(MVoidNullPtr);
      return Bounds;
    }

    case Instruction::ExtractElement: {
      auto *VBounds =
          dyn_cast<Constant>(getAssociatedBound(Expr->getOperand(0)));
      auto *Idx = Expr->getOperand(1);
      auto *EBound = ConstantExpr::getExtractElement(VBounds, Idx);
      Bounds.push_back(EBound);
      return Bounds;
    }

    case Instruction::InsertElement: {
      auto *VBounds =
          dyn_cast<Constant>(getAssociatedBound(Expr->getOperand(0)));
      auto *ElementBound = Expr->getOperand(1);
      auto *Idx = Expr->getOperand(2);
      auto *NewBounds =
          ConstantExpr::getInsertElement(VBounds, ElementBound, Idx);
      Bounds.push_back(NewBounds);
      return Bounds;
    }

    case Instruction::ExtractValue: {
      Value *AggOp = Expr->getOperand(0);
      auto VBounds = getAssociatedBounds(AggOp);

      size_t StartIdx =
          flattenAggregateIndices(AggOp->getType(), Expr->getIndices());
      size_t MetadataCount = countMetadata(Expr->getType());

      for (size_t J = StartIdx; J < StartIdx + MetadataCount; ++J) {
        Value *Bound = VBounds[J];
        Bounds.push_back(dyn_cast<T>(Bound));
      }

      return Bounds;
    }

    case Instruction::InsertValue: {
      Constant *AggOp = Expr->getOperand(0);
      Constant *ValOp = Expr->getOperand(1);

      auto AggBounds = getAssociatedBounds(AggOp);
      for (auto *Bound : AggBounds) {
        Bounds.push_back(dyn_cast<T>(Bound));
      }

      if (!isTypeWithPointers(ValOp->getType()))
        return Bounds;

      auto ValBounds = getAssociatedBounds(ValOp);
      size_t Idx =
          flattenAggregateIndices(AggOp->getType(), Expr->getIndices());

      for (unsigned J = 0; J < ValBounds.size(); ++J) {
        static_cast<MutableArrayRef<T *>>(Bounds)[Idx + J] =
            dyn_cast<T>(ValBounds[J]);
      }

      return Bounds;
    }
    }
  }
  if (auto *CAgg = dyn_cast<ConstantAggregate>(Const)) {
    if (auto *CArray = dyn_cast<ConstantArray>(CAgg)) {
      for (size_t i = 0; i < CArray->getType()->getNumElements(); i++) {
        auto CBounds =
            createConstantBounds<T>(CArray->getAggregateElement((unsigned)i));
        for (auto *Bound : CBounds) {
          Bounds.push_back(Bound);
        }
      }
      return Bounds;
    }

    if (auto *CVector = dyn_cast<ConstantVector>(CAgg)) {
      auto *VectorTy = CVector->getType();
      if (isVectorWithPointers(VectorTy)) {
        TinyPtrVector<Constant *> VecBounds;
        for (size_t i = 0; i < VectorTy->getNumElements(); i++) {
          auto ElBounds =
              createConstantBounds<Constant>(CVector->getAggregateElement(i));
          VecBounds.push_back(ElBounds.front());
        }
        auto *VecBound = ConstantVector::get(VecBounds);
        Bounds.push_back(VecBound);
      }
      return Bounds;
    }

    if (auto *CStruct = dyn_cast<ConstantStruct>(CAgg)) {
      for (size_t i = 0; i < CStruct->getType()->getNumElements(); i++) {
        auto ElBounds =
            createConstantBounds<T>(CStruct->getAggregateElement(i));
        for (auto *Bound : ElBounds) {
          Bounds.push_back(Bound);
        }
      }
      return Bounds;
    }
  }

  return Bounds;
}

template <typename T>
TinyPtrVector<T *> SoftBoundCETSPass::createConstantKeys(Constant *Const,
                                                         bool IsGlobal) {
  TinyPtrVector<T *> Keys;

  if (MValueKeyMap.count(Const)) {
    auto ConstKeys = MValueKeyMap[Const];
    for (auto *Key : ConstKeys) {
      Keys.push_back(dyn_cast<Constant>(Key));
    }
    return Keys;
  }

  if (isa<ConstantPointerNull>(Const)) {
    if (IsGlobal && ClAssociateZeroInitializedGlobalsWithOmnivalidMetadata)
      Keys.push_back(MConstantIntOne);
    else
      Keys.push_back(MConstantIntZero);
    return Keys;
  }
  if (isa<Function>(Const)) {
    Keys.push_back(MConstantIntOne);
    return Keys;
  }
  if (auto *Global = dyn_cast<GlobalValue>(Const)) {
    Keys.push_back(MConstantIntOne);
    return Keys;
  }
  if (auto *Undefined = dyn_cast<UndefValue>(Const)) {
    if (IsGlobal && ClAssociateZeroInitializedGlobalsWithOmnivalidMetadata)
      return createDummyMetadata<T>(Undefined->getType(), MConstantIntOne);
    return createDummyMetadata<T>(Undefined->getType(), MConstantIntZero);
  }
  if (auto *CAggZero = dyn_cast<ConstantAggregateZero>(Const)) {
    if (IsGlobal && ClAssociateZeroInitializedGlobalsWithOmnivalidMetadata)
      return createDummyMetadata<T>(CAggZero->getType(), MConstantIntOne);
    return createDummyMetadata<T>(CAggZero->getType(), MConstantIntZero);
  }
  if (ConstantExpr *Expr = dyn_cast<ConstantExpr>(Const)) {
    switch (Expr->getOpcode()) {
    case Instruction::GetElementPtr: {
      Constant *Op = cast<Constant>(Expr->getOperand(0));
      return createConstantKeys<T>(Op);
    }

    case BitCastInst::BitCast: {
      Constant *Op = cast<Constant>(Expr->getOperand(0));
      return createConstantKeys<T>(Op);
    }

    case Instruction::IntToPtr: {
      LLVM_DEBUG(errs() << "Unhandled IntToPtr operation: " << *Const << '\n');
      Keys.push_back(MConstantIntOne);
      return Keys;
    }
    }
  }
  if (auto *CAgg = dyn_cast<ConstantAggregate>(Const)) {
    if (auto *CArray = dyn_cast<ConstantArray>(CAgg)) {
      for (size_t i = 0; i < CArray->getType()->getNumElements(); i++) {
        auto CKeys =
            createConstantKeys<T>(CArray->getAggregateElement((unsigned)i));
        for (auto *Key : CKeys) {
          Keys.push_back(Key);
        }
      }
      return Keys;
    }

    if (auto *CVector = dyn_cast<ConstantVector>(CAgg)) {
      auto *VectorTy = CVector->getType();
      if (isVectorWithPointers(VectorTy)) {
        TinyPtrVector<Constant *> VecKeys;
        for (size_t i = 0; i < VectorTy->getNumElements(); i++) {
          auto ElKeys =
              createConstantKeys<Constant>(CVector->getAggregateElement(i));
          VecKeys.push_back(ElKeys.front());
        }
        auto *VecKey = ConstantVector::get(VecKeys);
        Keys.push_back(VecKey);
      }
      return Keys;
    }

    if (auto *CStruct = dyn_cast<ConstantStruct>(CAgg)) {
      for (size_t i = 0; i < CStruct->getType()->getNumElements(); i++) {
        auto ElKeys = createConstantKeys<T>(CStruct->getAggregateElement(i));
        for (auto *Key : ElKeys) {
          Keys.push_back(Key);
        }
      }
      return Keys;
    }
  }

  return Keys;
}

/*
 * This method computes the metadata for all pointers in a constant.
 * All generated metadata values will again be constants.
 * For global variables, the bound is GEP(global, 1).
 * No narrowing is performed for GEP constant expressions.
 */
void SoftBoundCETSPass::getConstantExprBaseBoundArray(
    Constant *Const, TinyPtrVector<Value *> &Bases,
    TinyPtrVector<Value *> &Bounds) {
  size_t NumPtrs = countPointersInType(Const->getType());

  if (NumPtrs == 0)
    return;

  if (isa<ConstantPointerNull>(Const) || isa<ConstantAggregateZero>(Const) ||
      isa<Function>(Const)) {
    for (unsigned i = 0; i < NumPtrs; ++i) {
      Bases.push_back(MVoidNullPtr);
      Bounds.push_back(MVoidNullPtr);
    }
    return;
  }

  if (GlobalVariable *Global = dyn_cast<GlobalVariable>(Const)) {
    Type *GlobalTy = Global->getValueType();
    Constant *GEPIdx =
        ConstantInt::get(Type::getInt32Ty(GlobalTy->getContext()), 1);
    Constant *Bound = ConstantExpr::getGetElementPtr(GlobalTy, Const, GEPIdx);

    Bases.push_back(Const);
    Bounds.push_back(Bound);
    return;
  }

  if (isa<ConstantAggregate>(Const)) {
    for (unsigned i = 0; i < Const->getNumOperands(); ++i) {
      Constant *El = cast<Constant>(Const->getOperand(i));
      getConstantExprBaseBoundArray(El, Bases, Bounds);
    }
    return;
  }

  if (ConstantExpr *Expr = dyn_cast<ConstantExpr>(Const)) {
    switch (Expr->getOpcode()) {
    case Instruction::GetElementPtr: {
      Constant *Op = cast<Constant>(Expr->getOperand(0));
      getConstantExprBaseBoundArray(Op, Bases, Bounds);
      return;
    }

    case BitCastInst::BitCast: {
      Constant *Op = cast<Constant>(Expr->getOperand(0));
      getConstantExprBaseBoundArray(Op, Bases, Bounds);
      return;
    }

    case Instruction::IntToPtr: {
      LLVM_DEBUG(errs() << "Unhandled IntToPtr operation: " << *Const << '\n');
      Bases.push_back(MVoidNullPtr);
      Bounds.push_back(MInfiniteBoundPtr);
      return;
    }
    }
  }

  LLVM_DEBUG(errs() << "Unhandled constant: " << *Const << '\n');
}
void SoftBoundCETSPass::identifyOriginalInst(Function *func) {
  for (Function::iterator bb_begin = func->begin(), bb_end = func->end();
       bb_begin != bb_end; ++bb_begin) {

    for (BasicBlock::iterator i_begin = bb_begin->begin(),
                              i_end = bb_begin->end();
         i_begin != i_end; ++i_begin) {

      Value *insn = dyn_cast<Value>(i_begin);
      if (!MPresentInOriginal.count(insn)) {
        MPresentInOriginal[insn] = 1;
      } else {
        assert(0 && "present in original map already has the insn?");
      }

      // if(isa<PointerType>(insn->getType())) {
      //   if(!m_is_pointer.count(insn)){
      //     m_is_pointer[insn] = 1;
      //   }
      // }
    } /* BasicBlock ends */
  }   /* Function ends */
}

bool SoftBoundCETSPass::runOnModule(Module &M) {
  if (!ClSpatialSafety && !ClTemporalSafety)
    return false;

  LLVM_DEBUG(dbgs() << "\n====================================================="
                       "====================\nSoftBoundCETS Pass:\n");

  DL = &M.getDataLayout();
  // TLI = &getAnalysis<TargetLibraryInfoWrapperPass>().getTLI();

  BuilderTy TheBuilder(M.getContext(), TargetFolder(*DL));

  Builder = &TheBuilder;
  C = &M.getContext();
  this->M = &M;

  const std::vector<std::string> BlacklistPaths = {BlacklistFile.str().str()};
  std::string Error;
  Blacklist =
      SpecialCaseList::create(BlacklistPaths, *vfs::getRealFileSystem(), Error);
  if (!Blacklist) {
    LLVM_DEBUG(errs() << "could not create blacklist: " << Error << "\n");
  }

  if (DL->getPointerSize() == 8) {
    m_is_64_bit = true;
  } else {
    m_is_64_bit = false;
  }
  initializeSoftBoundVariables(M);
  initializeInitFunctions(M);
  initializeDereferenceCheckHandlers(M);
  initializeMetadataHandlers(M);
  insertGlobalCtor(M);
  transformAndRedirectMain(M);
  identifyFuncToTrans(M);
  addMetadataToGlobals(M);

  for (Function &F : M.functions()) {
    LLVM_DEBUG(
        dbgs() << "\n====================================================="
                  "====================\n");

    if (!checkIfFunctionOfInterest(&F)) {
      LLVM_DEBUG(dbgs() << "Not instrumenting function: " << F.getName()
                        << "\n");
      continue;
    }

    LLVM_DEBUG(dbgs() << "Instrumenting function: " << F.getName() << "\n");
    InstrumentedFunctions.insert(&F);

    //
    // Iterating over the instructions in the function to identify IR
    // instructions in the original program In this pass, the pointers
    // in the original program are also identified
    //

    identifyOriginalInst(&F);

    //
    // Iterate over all basic block and then each insn within a basic
    // block We make two passes over the IR for base and bound
    // propagation and one pass for dereference checks
    //

    gatherBaseBoundPass1(F);
    gatherBaseBoundPass2(F);
    addDereferenceChecks(&F);

    llvm::StringRef PrintFns = ClPrintInstrumentedFunctions;
    if (ClPrintAllInstrumentedFunctions || PrintFns.contains(F.getName()))
      LLVM_DEBUG(dbgs() << "\nInstrumented Function: " << F << "\n");
  }

  renameFunctions(M);
  LLVM_DEBUG(dbgs() << "Done with SoftBoundCETSPass\n");

  return true;
}
