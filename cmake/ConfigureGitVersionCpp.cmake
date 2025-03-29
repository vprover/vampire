# GIT_COMMIT_DESCRIPTION used by version.cpp.in
execute_process(
  COMMAND git log -1 --format=%h\ on\ %ci
  WORKING_DIRECTORY ${VAMPIRE_SOURCE_DIR}
  OUTPUT_VARIABLE GIT_COMMIT_DESCRIPTION
  OUTPUT_STRIP_TRAILING_WHITESPACE
)
configure_file(${VAMPIRE_SOURCE_DIR}/version.cpp.in version.cpp)
