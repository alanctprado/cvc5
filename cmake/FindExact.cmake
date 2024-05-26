###############################################################################
# Top contributors (to current version):
# Alan Prado
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Find Exact
# Exact_FOUND - system has Exact lib
# Exact_INCLUDE_DIR - the Exact include directory
# Exact_LIBRARIES - Libraries needed to use Exact
##

include(deps-helper)
include(ExternalProject)

#TODO: add rules to use the user's installation of Exact if there is one
set(Exact_FOUND_SYSTEM FALSE)
if(NOT ENABLE_AUTO_DOWNLOAD)
  message(FATAL_ERROR "Could not find the required dependency Exact\
                      ${depname} in the system. Please use --auto-download to \
                      let us download and build it for you.")
endif()

#TODO: what is up with Exact's versioning?
set(Exact_VERSION "1.0.0")

if("${CMAKE_GENERATOR}" STREQUAL "Unix Makefiles")
  # use $(MAKE) instead of "make" to allow for parallel builds
  set(make_cmd "$(MAKE)")
else()
  # $(MAKE) does not work with ninja
  set(make_cmd "make")
endif()

ExternalProject_Add(
  Exact-EP
  ${COMMON_EP_CONFIG}
  URL "https://gitlab.com/api/v4/projects/25484789/repository/archive.tar.gz?sha=cb6ec0f9c843c974cc893e095976b27c7b3326dd"
  DOWNLOAD_NAME exact.tar.gz
  URL_HASH SHA256=2d68e05aecd57ee1803367b4e368c82502be867d95a06059543d1b0dc783bf9a
  PATCH_COMMAND ${SHELL} ${CMAKE_CURRENT_LIST_DIR}/deps-utils/exact-cb6ec0f-patch.sh <SOURCE_DIR>/CMakeLists.txt
  BUILD_IN_SOURCE YES
  CONFIGURE_COMMAND ${CMAKE_COMMAND} -B build -DCMAKE_BUILD_TYPE=Release -Dbuild_result=StaticLib -DCMAKE_POSITION_INDEPENDENT_CODE=ON -DCMAKE_INSTALL_PREFIX=<INSTALL_DIR>
  BUILD_COMMAND ${make_cmd} -C <SOURCE_DIR>/build
  INSTALL_COMMAND ${CMAKE_COMMAND} -E copy <SOURCE_DIR>/build/libExact.a ${DEPS_BASE}/lib/libExact.a
  BUILD_BYPRODUCTS <INSTALL_DIR>/build/libExact.a
)

set(Exact_INCLUDE_DIR "${DEPS_BASE}/src/")
set(Exact_LIBRARIES "${DEPS_BASE}/lib/libExact.a")

set(Exact_FOUND TRUE)

add_library(Exact STATIC IMPORTED GLOBAL)
set_target_properties(Exact PROPERTIES IMPORTED_LOCATION "${Exact_LIBRARIES}")
set_target_properties(Exact PROPERTIES INTERFACE_SYSTEM_INCLUDE_DIRECTORIES "${Exact_INCLUDE_DIR}")

mark_as_advanced(Exact_FOUND)
mark_as_advanced(Exact_FOUND_SYSTEM)
mark_as_advanced(Exact_INCLUDE_DIR)
mark_as_advanced(Exact_LIBRARIES)

add_dependencies(Exact Exact-EP)
