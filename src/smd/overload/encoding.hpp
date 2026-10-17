// encoding.hpp                                                       -*-C++-*-
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
#ifndef INCLUDED_ENCODING
#define INCLUDED_ENCODING

// The typeclass encoding under study, reduced to the fragment the model
// covers. It mirrors the mechanism of beman.transpose (functor.hpp and
// detail/typeclass_base.hpp in github.com/bemanproject/typeclass), which is
// the reference implementation: a lookup variable template per typeclass
// with std::false_type as the default instance, a derivation base that
// supplies the derived operations from an instance's primitives, and an
// operation object that resolves the instance at the call site through a
// trailing defaulted constant template parameter.
//
// Each piece is here so that the emitted differential tests and the probes
// can refer to one spelling, and so that the obligations table in
// docs/plan.md has code to point at: soft failure of a missing instance is
// the std::false_type default plus the constraint on the operation object.

#include <string_view>
#include <type_traits>
#include <utility>

namespace overload {

// 44cc988c-7353-43aa-a7d3-8840f92371a6
/** The canonical Functor lookup. Specialize for each type that has an
 * instance; the primary is the default instance, std::false_type, so that
 * a type without an instance is a soft failure at the use, never a hard
 * error inside the lookup. */
template <class T>
inline constexpr auto functor = std::false_type{};

/** True when a lookup has been specialized away from its default: the
 * type has an instance. Pass decltype(functor<T>). */
template <class LOOKUP_RESULT>
inline constexpr bool has_instance_v =
    !std::is_same_v<std::remove_cvref_t<LOOKUP_RESULT>, std::false_type>;

/** The type has a Functor instance. */
template <class T>
concept has_functor = has_instance_v<decltype(functor<T>)>;
// 44cc988c-7353-43aa-a7d3-8840f92371a6 end

namespace detail {
/** The function that ignores its argument and returns `value`: what
 * `replace` maps with. A named type, not a lambda, because it appears in
 * `replace`'s constraint. */
template <class VALUE>
struct constant_function {
    VALUE value;

    template <class ARGUMENT>
    constexpr auto operator()(const ARGUMENT &) const -> VALUE {
        return value;
    }
};
} // namespace detail

/** Derivation base for Functor instances. `Impl` supplies `fmap(f, v)`;
 * `replace` is derived from it unless `Impl` supplies its own. `Impl` is a
 * protected base, as in beman.transpose, so the instance exposes only the
 * operations this base declares. */
template <class Impl>
struct derive_functor : protected Impl {
    template <class FUNCTION, class T>
    constexpr auto fmap(FUNCTION &&function, T &&value) const
        requires requires(const Impl &impl) {
            impl.fmap(std::forward<FUNCTION>(function), std::forward<T>(value));
        }
    {
        return Impl::fmap(std::forward<FUNCTION>(function),
                          std::forward<T>(value));
    }

    template <class T, class U>
    constexpr auto replace(T &&value, U &&replacement) const
        requires requires(const Impl &impl) {
            impl.replace(std::forward<T>(value), std::forward<U>(replacement));
        } || requires(const Impl &impl) {
            impl.fmap(
                detail::constant_function<std::remove_cvref_t<U>>{
                    std::forward<U>(replacement)},
                std::forward<T>(value));
        }
    {
        if constexpr (requires(const Impl &impl) {
                          impl.replace(std::forward<T>(value),
                                       std::forward<U>(replacement));
                      }) {
            return Impl::replace(std::forward<T>(value),
                                 std::forward<U>(replacement));
        } else {
            return Impl::fmap(
                detail::constant_function<std::remove_cvref_t<U>>{
                    std::forward<U>(replacement)},
                std::forward<T>(value));
        }
    }
};

// 5cdef435-de62-4973-91f4-a56dbef659f3
/** The operation object for `fmap`. The container type keys the lookup
 * and is deduced from the second argument; the instance arrives through
 * the trailing constant template parameter, a reference defaulted to the
 * lookup. The constraint is the call itself, as in beman.transpose, so a
 * type without an instance is not a candidate. The default is substituted
 * before the constraint is checked ([temp.deduct.general]/5), which is the
 * step-order hazard of the plan: it is safe here only because the lookup's
 * default is std::false_type, which has no `fmap`. */
inline constexpr struct fmap_t {
    template <class FUNCTION, class T,
              const auto &TC = functor<std::remove_cvref_t<T>>>
        requires requires {
            TC.fmap(std::declval<FUNCTION>(), std::declval<T>());
        }
    constexpr auto operator()(FUNCTION &&function, T &&value) const {
        return TC.fmap(std::forward<FUNCTION>(function),
                       std::forward<T>(value));
    }
} fmap{};
// 5cdef435-de62-4973-91f4-a56dbef659f3 end

/** The document number of the draft every citation in the model is read
 * against, so that the installed package and the model agree on it. */
std::string_view draft_pin();

} // namespace overload

#endif // INCLUDED_ENCODING
