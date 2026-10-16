// probes/step_order_variable.cpp                                     -*-C++-*-
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
// Step-order probe, variant B only, with the lookup routed through a
// variable template as the modelled library does (`functor<T>` in
// beman.transpose) rather than through a class template's static member.
// Records a finding of the reconstruction: the undefined-primary soft route
// of docs/probes.md depends on the spelling of the lookup. Here the
// variable template specialization is a separate instantiation, so its
// failure is outside the immediate context.

struct X {};

template <class T>
struct functor_instance;

template <class T>
inline constexpr auto functor = functor_instance<T>::value;

template <class T, const auto &TC = functor<T>>
int f(T, int) {
    return 1;
}

int f(X, int) { return 2; }

int main() { return f(X{}, 0) == 2 ? 0 : 1; }
