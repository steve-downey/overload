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

#include <beman/transpose.hpp>

#include <array>
#include <expected>
#include <memory>
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

// Callables an algorithm might pass on to an instance member, for the
// parametricity probes. Each is a reasonable thing for a user to hand an
// algorithm; the probe asks whether every instance that accepts the
// concept's witness also accepts it.
inline constexpr auto by_cref = [](const int &x) { return x + 1; };
inline constexpr auto generic = [](auto x) { return x + 1; };
inline constexpr auto by_rref = [](int &&x) { return x + 1; };
inline constexpr auto ret_void = [](int) {};
inline constexpr auto ret_ref = [](const int &x) -> const int & { return x; };
inline constexpr int (*fn_ptr)(int) = [](int x) { return x + 1; };
struct move_only {
    std::unique_ptr<int> p;
    auto operator()(int x) const -> int { return x; }
};
struct mutable_fn {
    int n = 0;
    auto operator()(int x) -> int { return x + n++; }
};
struct move_only_opt {
    std::unique_ptr<int> p;
    auto operator()(int x) const -> std::optional<int> { return x; }
};
struct mutable_opt {
    int n = 0;
    auto operator()(int x) -> std::optional<int> { return x + n++; }
};
inline constexpr auto generic_opt = [](auto x) { return std::optional{x}; };
inline constexpr std::optional<int> (*fn_ptr_opt)(int) = [](int x) {
    return std::optional<int>{x};
};
inline constexpr auto inc_exp = [](int x) { return exp_t{x + 1}; };

using acc_t =
    std::remove_cvref_t<decltype(bt::accumulating_applicative<exp_t>)>;
using app_opt_t = std::remove_cvref_t<decltype(bt::applicative<opt>)>;
using monad_opt_t = std::remove_cvref_t<decltype(bt::monad<opt>)>;
using app_exp_t = std::remove_cvref_t<decltype(bt::applicative<exp_t>)>;
using monad_exp_t = std::remove_cvref_t<decltype(bt::monad<exp_t>)>;
using functor_base_t = bt::derive_functor<bt::OptionalFunctorImpl<int>>;

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
