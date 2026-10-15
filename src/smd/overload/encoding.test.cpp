// overload/encoding.test.cpp                                              -*-C++-*-
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

#include <smd/overload/encoding.hpp>

#include <smd/overload/encoding.hpp> // test 2nd include OK

#include <catch2/catch_test_macros.hpp>

// 03013d1f-bcc1-4d3e-9701-3ed1a15c6370
TEST_CASE("encoding returns Steve", "encoding") {
    REQUIRE(overload::encoding() == "Steve");
}
// 03013d1f-bcc1-4d3e-9701-3ed1a15c6370 end
