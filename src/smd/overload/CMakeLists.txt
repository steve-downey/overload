include(GNUInstallDirs)

target_sources(
    overload.encoding
    PUBLIC FILE_SET overload_encoding_headers TYPE HEADERS FILES encoding.hpp
    PRIVATE encoding.cpp
)

## Tests
if(ENCODING_ENABLE_TESTING AND NOT Catch2_FOUND)
    find_package(Catch2 3 QUIET)
    if(Catch2_FOUND)
        include(Catch)
    else()
        message(
            WARNING
            "
No provider for Catch2. Unable to build tests.
Consider using CMAKE_PROJECT_TOP_LEVEL_INCLUDES=./cmake/use-fetch-content.cmake as documented in the README.md
"
        )
    endif()
endif()

if(ENCODING_ENABLE_TESTING)
    add_executable(encoding_test)

    target_sources(encoding_test PRIVATE encoding.test.cpp)

    target_link_libraries(encoding_test overload.encoding)
    target_link_libraries(encoding_test Catch2::Catch2WithMain)

    include(Catch)
    catch_discover_tests(encoding_test)
endif()
