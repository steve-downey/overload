// probes/tie_break.cpp                                               -*-C++-*-
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
// Tie-break probe. Two overloads where the second is more constrained,
// varying how the instance bound is written. [temp.func.order]/8 compares
// constraints only when the template parameter lists are equivalent, and
// [temp.over.link]/6 says equivalence of constant parameters ignores
// type-constraints on placeholder types. Compile with -DVARIANT=<letter>.
//
// Reconstructed from the plan's descriptions; see step_order.cpp.

#include <type_traits>

#ifndef VARIANT
#define VARIANT 'A'
#endif

struct instance {
    int fmap = 0;
};

template <class T>
inline constexpr instance functor{};

template <class T>
concept shape = requires(const T &t) { t.fmap; };

template <class T>
concept c1 = std::is_class_v<T>;

template <class T>
concept c2 = c1<T> && std::is_empty_v<T>;

struct X {};

#if VARIANT == 'A'
// requires-clauses only; the heads are equivalent, so the tie-break applies.
template <class T>
    requires c1<T>
int g(T) {
    return 1;
}
template <class T>
    requires c2<T>
int g(T) {
    return 2;
}
#elif VARIANT == 'B'
// #2 has an extra defaulted template parameter: the lists differ in length.
template <class T>
    requires c1<T>
int g(T) {
    return 1;
}
template <class T, const auto &TC = functor<T>>
    requires c2<T>
int g(T) {
    return 2;
}
#elif VARIANT == 'C'
// The bound is a type-constraint on an auto constant parameter.
// [temp.over.link]/6: equivalence ignores it, so the heads stay equivalent.
template <class T, const auto &TC = functor<T>>
    requires c1<T>
int g(T) {
    return 1;
}
template <class T, const shape auto &TC = functor<T>>
    requires c2<T>
int g(T) {
    return 2;
}
#elif VARIANT == 'D'
// Constant parameters of different concrete instance types: not equivalent.
struct other_instance {
    int fmap = 0;
};
template <class T>
inline constexpr other_instance other_functor{};
template <class T, const instance &TC = functor<T>>
    requires c1<T>
int g(T) {
    return 1;
}
template <class T, const other_instance &TC = other_functor<T>>
    requires c2<T>
int g(T) {
    return 2;
}
#endif

int main() { return g(X{}) == 2 ? 0 : 1; }
