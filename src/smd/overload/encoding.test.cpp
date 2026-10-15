// overload/encoding.test.cpp                                         -*-C++-*-
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

#include <smd/overload/encoding.hpp>

#include <smd/overload/encoding.hpp> // test 2nd include OK

#include <catch2/catch_test_macros.hpp>

#include <string>

namespace {

template <class T>
struct box {
    T value;
    constexpr bool operator==(const box &) const = default;
};

struct box_functor_impl {
    template <class FUNCTION, class T>
    static constexpr auto fmap(FUNCTION &&function, const box<T> &b) {
        return box<decltype(function(b.value))>{function(b.value)};
    }
};

struct no_instance {};

} // namespace

template <class T>
inline constexpr overload::derive_functor<box_functor_impl>
    overload::functor<box<T>>{};

// 03013d1f-bcc1-4d3e-9701-3ed1a15c6370
TEST_CASE("the draft pin names the text the model cites", "[encoding]") {
    REQUIRE(overload::draft_pin() == "N5054");
}
// 03013d1f-bcc1-4d3e-9701-3ed1a15c6370 end

TEST_CASE("a type without an instance has the default", "[encoding]") {
    STATIC_REQUIRE(!overload::has_functor<no_instance>);
    STATIC_REQUIRE(!overload::has_functor<int>);
    STATIC_REQUIRE(overload::has_functor<box<int>>);
}

TEST_CASE("the operation object resolves the instance at the call",
          "[encoding]") {
    constexpr box<int> b{20};
    STATIC_REQUIRE(overload::fmap([](int i) { return i + 1; }, b) ==
                   box<int>{21});
    REQUIRE(overload::fmap([](int i) { return std::to_string(i); }, b) ==
            box<std::string>{"20"});
}

TEST_CASE("a missing instance is a soft failure: the call does not match",
          "[encoding]") {
    STATIC_REQUIRE(
        !std::is_invocable_v<overload::fmap_t,
                             decltype([](int i) { return i; }), no_instance>);
    STATIC_REQUIRE(
        std::is_invocable_v<overload::fmap_t, decltype([](int i) { return i; }),
                            box<int>>);
}

TEST_CASE("replace is derived from fmap", "[encoding]") {
    constexpr box<int> b{20};
    STATIC_REQUIRE(overload::functor<box<int>>.replace(b, 'x') ==
                   box<char>{'x'});
}
