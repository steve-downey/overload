// probes/library/prelude.hpp                                         -*-C++-*-
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
// Shared by every library probe. A probe asks whether one call into
// beman.transpose is a valid expression. The call is the body of a
// requires-expression in a concept, with its arguments made dependent on the
// concept's parameter through a member typedef, so that it is checked when
// the concept is used rather than when it is defined. An alias template that
// discards its first argument is not enough: Clang treats it as the type it
// names.
//
// The probe compiles when the call is not a valid expression (soft), fails
// with the single static_assert below when it is (valid), and fails any
// other way when checking it is a hard error.

#include <beman/transpose/transpose.hpp>

#include <array>
#include <expected>
#include <optional>
#include <string>
#include <vector>

namespace bt = beman::transpose;

struct nope {};
struct not_callable {};

using opt = std::optional<int>;
using vec = std::vector<int>;
using exp_t = std::expected<int, std::string>;
using arr = std::array<int, 3>;

inline constexpr auto inc = [](int x) { return x + 1; };
inline constexpr auto inc_opt = [](int x) { return std::optional<int>{x + 1}; };

template <class D, class T>
struct depw {
    using type = T;
};

// clang-format off
#define DEP(...) typename depw<Dummy, __VA_ARGS__>::type
#define PROBE(...)                                                            \
    template <class Dummy>                                                    \
    concept probe = requires { __VA_ARGS__; };                                \
    static_assert(!probe<void>, "PROBE_TRUE");
// clang-format on
