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
# Find RoundingSat
# RoundingSat_FOUND - system has RoundingSat lib
# RoundingSat_INCLUDE_DIR - the RoundingSat include directory
# RoundingSat_LIBRARIES - Libraries needed to use RoundingSat
##

include(deps-helper)
include(ExternalProject)

#TODO: add rules to use the user's installation of RoundingSAT (if there is one)
set(RoundingSat_FOUND_SYSTEM FALSE)
if(NOT ENABLE_AUTO_DOWNLOAD)
  message(FATAL_ERROR "Could not find the required dependency RoundingSat \
                      ${depname} in the system. Please use --auto-download to \
                      let us download and build it for you.")
endif()

#TODO: figure out RoundingSat's version
set(RoundingSat_VERSION "1.0.0")

if("${CMAKE_GENERATOR}" STREQUAL "Unix Makefiles")
  # use $(MAKE) instead of "make" to allow for parallel builds
  set(make_cmd "$(MAKE)")
else()
  # $(MAKE) does not work with ninja
  set(make_cmd "make")
endif()

if(NOT EXISTS "${DEPS_BASE}/bin")
  file(MAKE_DIRECTORY "${DEPS_BASE}/bin")
endif()

# ---------------------------------------------------------------------------------------------------------------------------------

ExternalProject_Add(
  RoundingSat-EP
  ${COMMON_EP_CONFIG}
  URL "https://gitlab.com/api/v4/projects/16394380/repository/archive.tar.gz?sha=d34b6bed0ea5e0a54189650ee5acf5fcaa6b8581"
  DOWNLOAD_NAME roundingsat.tar.gz
  URL_HASH SHA256=85ba9da0429be6998287820f7d268390745d612757f2f8f2d35a5bcab8ae2098
  PATCH_COMMAND ${SHELL} ${CMAKE_CURRENT_LIST_DIR}/deps-utils/roundingsat-d34b6be-patch.sh <SOURCE_DIR>/CMakeLists.txt
  BUILD_IN_SOURCE YES
  CONFIGURE_COMMAND ${CMAKE_COMMAND} -B build -DCMAKE_BUILD_TYPE=Release -Dbuild_result=StaticLib -DCMAKE_POSITION_INDEPENDENT_CODE=ON -DCMAKE_INSTALL_PREFIX=<INSTALL_DIR>
  BUILD_COMMAND ${make_cmd} -C <SOURCE_DIR>/build
  INSTALL_COMMAND ${CMAKE_COMMAND} -E copy <SOURCE_DIR>/build/roundingsat ${DEPS_BASE}/bin/roundingsat
  BUILD_BYPRODUCTS <INSTALL_DIR>/build/roundingsat
)

add_compile_definitions(ROUNDINGSAT_PATH="${DEPS_BASE}/bin/roundingsat")

set(RoundingSat_FOUND TRUE)
mark_as_advanced(RoundingSat_FOUND)
mark_as_advanced(RoundingSat_FOUND_SYSTEM)
