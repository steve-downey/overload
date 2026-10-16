// probes/step_order.cpp                                              -*-C++-*-
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
// Step-order probe. A candidate with a defaulted constant template parameter
// whose default performs an instance lookup, where the lookup fails with a
// static_assert for the argument type, alongside a second candidate that
// should win. Compile with -DVARIANT=<letter>; see probes/run.sh and
// docs/probes.md for the outcomes per compiler.
//
// Reconstructed from the descriptions in the plan of 13 October 2026; the
// original probe sources were not in the repository. The reconstruction is
// checked by reproducing the plan's results table on the same compilers.
// The lookup is spelled as a static member of a class template,
// `functor_instance<T>::value`, because that is the spelling under which
// variant B reproduces: an undefined primary used in the default argument
// is an invalid expression in the immediate context. Routed through a
// variable template, `functor<T>`, the same undefined primary is a hard
// error on Clang, since the variable template's initializer is a separate
// instantiation (docs/probes.md).

#include <type_traits>

#ifndef VARIANT
#define VARIANT 'A'
#endif

struct X {};

struct instance {
    int fmap = 0;
};

#if VARIANT == 'B'
// An undefined primary template: the lookup's operand is an incomplete type.
template <class T>
struct functor_instance;
#elif VARIANT == 'D'
// The library's own design: the default instance is std::false_type and the
// candidate is constrained on the shape of what the lookup found.
template <class T>
struct functor_instance {
    static constexpr std::false_type value{};
};
#else
// The hard-failing lookup: instantiating the instance for a type that has
// none fires a static_assert, outside any immediate context.
template <class T>
struct functor_instance {
    static_assert(sizeof(T) == 0, "no functor instance for this type");
    static constexpr instance value{};
};
#endif

#if VARIANT == 'C'
template <class T>
concept has_instance = requires { functor_instance<T>::value.fmap; };
#endif

// ---- candidate #1: the template whose default argument does the lookup ----

#if VARIANT == 'A' || VARIANT == 'B' || VARIANT == 'G' || VARIANT == 'I'
template <class T, const auto &TC = functor_instance<T>::value>
int f(T, int) {
    return 1;
}
#elif VARIANT == 'C'
// A requires-clause on the same template cannot guard the default: the
// default is substituted first ([temp.deduct.general]/5).
template <class T, const auto &TC = functor_instance<T>::value>
    requires has_instance<T>
int f(T, int) {
    return 1;
}
#elif VARIANT == 'D'
template <class T, const auto &TC = functor_instance<T>::value>
    requires(
        !std::is_same_v<std::remove_cvref_t<decltype(TC)>, std::false_type>)
int f(T, int) {
    return 1;
}
#elif VARIANT == 'E'
// The lookup is in a default function argument, which is instantiated only
// if the candidate is selected and the argument is needed.
template <class T>
int f(T, int, const void * = &functor_instance<T>::value) {
    return 1;
}
#elif VARIANT == 'H'
// The lookup is in the return type: substituted as part of the function type.
template <class T>
auto f(T, int) -> decltype(functor_instance<T>::value, 1) {
    return 1;
}
#endif

// ---- candidate #2: the one that should win ----

#if VARIANT == 'G'
// A worse match: int -> long is a conversion, so the template competes on
// deduction and the lookup runs.
int f(X, long) { return 2; }
#elif VARIANT == 'I'
// A more specialized template, exact match. It wins partial ordering, but
// candidate #1 still has its default substituted.
template <class T>
struct wrap {};
template <class T>
int f(wrap<T>, int) {
    return 2;
}
#else
// A non-template exact match.
int f(X, int) { return 2; }
#endif

int main() {
#if VARIANT == 'I'
    return f(wrap<X>{}, 0) == 2 ? 0 : 1;
#else
    return f(X{}, 0) == 2 ? 0 : 1;
#endif
}
