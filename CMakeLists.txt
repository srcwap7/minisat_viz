cmake_minimum_required(VERSION 2.6 FATAL_ERROR)
project(minisat)

option(STATIC_BINARIES "Link binaries statically." ON)
option(USE_SORELEASE   "Use SORELEASE in shared library filename." ON)

set(MINISAT_SOMAJOR   2)
set(MINISAT_SOMINOR   1)
set(MINISAT_SORELEASE 0)

if (USE_SORELEASE)
  set(MINISAT_VERSION ${MINISAT_SOMAJOR}.${MINISAT_SOMINOR}.${MINISAT_SORELEASE})
else()
  set(MINISAT_VERSION ${MINISAT_SOMAJOR}.${MINISAT_SOMINOR})
endif()
set(MINISAT_SOVERSION ${MINISAT_SOMAJOR})

find_package(ZLIB REQUIRED)
find_package(Python3 COMPONENTS Interpreter Development REQUIRED)

include_directories(${ZLIB_INCLUDE_DIR})
include_directories(${Python3_INCLUDE_DIRS})
include_directories(${minisat_SOURCE_DIR})

add_definitions(-D__STDC_FORMAT_MACROS -D__STDC_LIMIT_MACROS)

set(MINISAT_LIB_SOURCES
    minisat/utils/Options.cc
    minisat/utils/System.cc
    minisat/core/Solver.cc
    minisat/simp/SimpSolver.cc
)

add_library(minisat-lib-static STATIC ${MINISAT_LIB_SOURCES})
add_library(minisat-lib-shared SHARED ${MINISAT_LIB_SOURCES})

target_link_libraries(minisat-lib-shared ${ZLIB_LIBRARY} ${Python3_LIBRARIES})
target_link_libraries(minisat-lib-static ${ZLIB_LIBRARY} ${Python3_LIBRARIES})

add_executable(minisat_core minisat/core/Main.cc)
add_executable(minisat_simp minisat/simp/Main.cc)

if(STATIC_BINARIES)
  target_link_libraries(minisat_core minisat-lib-static ${Python3_LIBRARIES})
  target_link_libraries(minisat_simp minisat-lib-static ${Python3_LIBRARIES})
else()
  target_link_libraries(minisat_core minisat-lib-shared ${Python3_LIBRARIES})
  target_link_libraries(minisat_simp minisat-lib-shared ${Python3_LIBRARIES})
endif()

set_target_properties(minisat-lib-static PROPERTIES OUTPUT_NAME "minisat")
set_target_properties(minisat-lib-shared
  PROPERTIES
    OUTPUT_NAME "minisat"
    VERSION ${MINISAT_VERSION}
    SOVERSION ${MINISAT_SOVERSION})

set_target_properties(minisat_simp PROPERTIES OUTPUT_NAME "minisat")

# -----------------------------------------
# Simple visualizer (fixed)
# -----------------------------------------
add_executable(simple_visualizer minisat/core/comparative_analysis.cc)

if(STATIC_BINARIES)
  target_link_libraries(simple_visualizer minisat-lib-static ${Python3_LIBRARIES})
else()
  target_link_libraries(simple_visualizer minisat-lib-shared ${Python3_LIBRARIES})
endif()

install(TARGETS minisat-lib-static minisat-lib-shared minisat_core minisat_simp 
        RUNTIME DESTINATION bin
        LIBRARY DESTINATION lib
        ARCHIVE DESTINATION lib)

install(DIRECTORY minisat/mtl minisat/utils minisat/core minisat/simp
        DESTINATION include/minisat
        FILES_MATCHING PATTERN "*.h")

message(STATUS "-------------------------------------------------------------")
message(STATUS " MiniSAT build configuration")
message(STATUS "   Python3 include dirs : ${Python3_INCLUDE_DIRS}")
message(STATUS "   Python3 libraries    : ${Python3_LIBRARIES}")
message(STATUS "   ZLIB include dir     : ${ZLIB_INCLUDE_DIR}")
message(STATUS "-------------------------------------------------------------")
