set(SOFTBOUNDCETS_SOURCES
	softboundcets.cpp
	softboundcets-wrappers.cpp
)

set(SOFTBOUNDCETS_HEADERS
	softboundcets.h
)

set(SOFTBOUNDCETS_COMMON_CFLAGS ${SANITIZER_COMMON_CFLAGS} -D__SOFTBOUNDCETS_SPATIAL_TEMPORAL=1 -O2)

set(SOFTBOUNDCETS_STANDARD_CFLAGS ${SOFTBOUNDCETS_COMMON_CFLAGS} -DLOG_LEVEL=3 -g)
set(SOFTBOUNDCETS_DYNAMIC_CFLAGS ${SOFTBOUNDCETS_COMMON_CFLAGS} -D__SOFTBOUNDCETS_DYNAMIC_RT=1 -DLOG_LEVEL=3 -O0 -g)
set(SOFTBOUNDCETS_INLINING_CFLAGS ${SOFTBOUNDCETS_COMMON_CFLAGS} -flto -g0)
set(SOFTBOUNDCETS_BENCHMARK_CFLAGS ${SOFTBOUNDCETS_COMMON_CFLAGS} -D__SOFTBOUNDCETS_BENCHMARKING=1 -g -O3)
set(SOFTBOUNDCETS_BENCHMARK_INLINING_CFLAGS ${SOFTBOUNDCETS_COMMON_CFLAGS} -D__SOFTBOUNDCETS_BENCHMARKING=1 -flto -O3 -g0)
set(SOFTBOUNDCETS_BENCHMARK_INLINING_INVALID_LOCKS_CFLAGS ${SOFTBOUNDCETS_COMMON_CFLAGS} -D__SOFTBOUNDCETS_BENCHMARKING=1 -D__SOFTBOUNDCETS_PREVENT_SEGFAULTS_ON_INVALID_LOCKS=1 -flto -O3 -g0)

append_rtti_flag(OFF SANITIZER_COMMON_CFLAGS)

set(SOFTBOUNDCETS_DYNAMIC_LINK_FLAGS ${SANITIZER_COMMON_LINK_FLAGS})
set(SOFTBOUNDCETS_DYNAMIC_LIBS ${SANITIZER_CXX_ABI_LIBRARIES} ${SANITIZER_COMMON_LINK_LIBS})

append_list_if(COMPILER_RT_HAS_LIBDL dl SOFTBOUNDCETS_DYNAMIC_LIBS)
append_list_if(COMPILER_RT_HAS_LIBRT rt SOFTBOUNDCETS_DYNAMIC_LIBS)
append_list_if(COMPILER_RT_HAS_LIBM m SOFTBOUNDCETS_DYNAMIC_LIBS)
append_list_if(COMPILER_RT_HAS_LIBPTHREAD pthread SOFTBOUNDCETS_DYNAMIC_LIBS)
append_list_if(COMPILER_RT_HAS_LIBLOG log SOFTBOUNDCETS_DYNAMIC_LIBS)



add_compiler_rt_component(softboundcets)

add_compiler_rt_object_libraries(RTsoftboundcets_dynamic
  OS ${SANITIZER_COMMON_SUPPORTED_OS}
  ARCHS ${SOFTBOUNDCETS_SUPPORTED_ARCH}
  SOURCES ${SOFTBOUNDCETS_SOURCES}
  ADDITIONAL_HEADERS ${SOFTBOUNDCETS_HEADERS}
  CFLAGS ${SOFTBOUNDCETS_DYNAMIC_CFLAGS})


add_compiler_rt_object_libraries(RTsoftboundcets
	ARCHS ${SOFTBOUNDCETS_SUPPORTED_ARCH}
	SOURCES ${SOFTBOUNDCETS_SOURCES}
	ADDITIONAL_HEADERS ${SOFTBOUNDCETS_HEADERS}
	CFLAGS ${SOFTBOUNDCETS_STANDARD_CFLAGS}
)

add_compiler_rt_object_libraries(RTsoftboundcets_benchmark
	ARCHS ${SOFTBOUNDCETS_SUPPORTED_ARCH}
	SOURCES ${SOFTBOUNDCETS_SOURCES}
	ADDITIONAL_HEADERS ${SOFTBOUNDCETS_HEADERS}
	CFLAGS ${SOFTBOUNDCETS_BENCHMARK_CFLAGS}
)

add_compiler_rt_object_libraries(RTsoftboundcets_inlining
	ARCHS ${SOFTBOUNDCETS_SUPPORTED_ARCH}
	SOURCES ${SOFTBOUNDCETS_SOURCES}
	ADDITIONAL_HEADERS ${SOFTBOUNDCETS_HEADERS}
	CFLAGS ${SOFTBOUNDCETS_INLINING_CFLAGS}
)

add_compiler_rt_object_libraries(RTsoftboundcets_benchmark_inlining
	ARCHS ${SOFTBOUNDCETS_SUPPORTED_ARCH}
	SOURCES ${SOFTBOUNDCETS_SOURCES}
	ADDITIONAL_HEADERS ${SOFTBOUNDCETS_HEADERS}
	CFLAGS ${SOFTBOUNDCETS_BENCHMARK_INLINING_CFLAGS}
)

add_compiler_rt_object_libraries(RTsoftboundcets_benchmark_inlining_invalid_locks
	ARCHS ${SOFTBOUNDCETS_SUPPORTED_ARCH}
	SOURCES ${SOFTBOUNDCETS_SOURCES}
	ADDITIONAL_HEADERS ${SOFTBOUNDCETS_HEADERS}
	CFLAGS ${SOFTBOUNDCETS_BENCHMARK_INLINING_INVALID_LOCKS_CFLAGS}
)



include_directories(..)

foreach(arch ${SOFTBOUNDCETS_SUPPORTED_ARCH})
    add_compiler_rt_runtime(clang_rt.softboundcets
      STATIC
      ARCHS ${arch}
      OBJECT_LIBS RTsoftboundcets
                  RTInterception
                  RTSanitizerCommon
                  RTSanitizerCommonLibc
                  RTSanitizerCommonCoverage
                  RTSanitizerCommonSymbolizer
      CFLAGS ${SOFTBOUNDCETS_COMMON_CFLAGS}
      PARENT_TARGET softboundcets)

    add_compiler_rt_runtime(clang_rt.softboundcets_benchmark
      STATIC
      ARCHS ${arch}
      OBJECT_LIBS RTsoftboundcets_benchmark
                  RTInterception
                  RTSanitizerCommon
                  RTSanitizerCommonLibc
                  RTSanitizerCommonCoverage
                  RTSanitizerCommonSymbolizer
      CFLAGS ${SOFTBOUNDCETS_BENCHMARK_CFLAGS}
      PARENT_TARGET softboundcets)

    add_compiler_rt_runtime(clang_rt.softboundcets_inlining
      STATIC
      ARCHS ${arch}
      OBJECT_LIBS RTsoftboundcets_inlining
                  RTInterception
                  RTSanitizerCommon
                  RTSanitizerCommonLibc
                  RTSanitizerCommonCoverage
                  RTSanitizerCommonSymbolizer
      CFLAGS ${SOFTBOUNDCETS_INLINING_CFLAGS}
      PARENT_TARGET softboundcets)

    add_compiler_rt_runtime(clang_rt.softboundcets_benchmark_inlining
      STATIC
      ARCHS ${arch}
      OBJECT_LIBS RTsoftboundcets_benchmark_inlining
                  RTInterception
                  RTSanitizerCommon
                  RTSanitizerCommonLibc
                  RTSanitizerCommonCoverage
                  RTSanitizerCommonSymbolizer
      CFLAGS ${SOFTBOUNDCETS_BENCHMARK_INLINING_CFLAGS}
      PARENT_TARGET softboundcets)

    add_compiler_rt_runtime(clang_rt.softboundcets_benchmark_inlining_invalid_locks
      STATIC
      ARCHS ${arch}
      OBJECT_LIBS RTsoftboundcets_benchmark_inlining_invalid_locks
                  RTInterception
                  RTSanitizerCommon
                  RTSanitizerCommonLibc
                  RTSanitizerCommonCoverage
                  RTSanitizerCommonSymbolizer
      CFLAGS ${SOFTBOUNDCETS_BENCHMARK_INLINING_INVALID_LOCKS_CFLAGS}
      PARENT_TARGET softboundcets)

  add_compiler_rt_runtime(clang_rt.softboundcets
      SHARED
      ARCHS ${arch}
      OBJECT_LIBS RTsoftboundcets_dynamic
                  RTInterception
                  RTSanitizerCommon
                  RTSanitizerCommonLibc
                  RTSanitizerCommonCoverage
                  RTSanitizerCommonSymbolizer
      CFLAGS ${SOFTBOUNDCETS_DYNAMIC_CFLAGS}
      LINK_FLAGS ${SOFTBOUNDCETS_DYNAMIC_LINK_FLAGS}
      LINK_LIBS ${SOFTBOUNDCETS_DYNAMIC_LIBS}
      ADDITIONAL_HEADERS ${SOFTBOUNDCETS_HEADERS}
      PARENT_TARGET softboundcets)

endforeach()
