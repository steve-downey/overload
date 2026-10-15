// probes/constant_conversion.cpp                                     -*-C++-*-
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
// Constant-argument conversion probe. A derived-class value supplied for a
// base-typed class-type constant template parameter. [temp.arg.nontype]/1
// and /3 as rewritten by P2308R1 govern. Compile with -DVARIANT=<letter>.
//
// Reconstructed from the plan's descriptions; see step_order.cpp.

#include <type_traits>

#ifndef VARIANT
#define VARIANT 'A'
#endif

struct base {
    int v;
    constexpr explicit base(int v) : v(v) {}
    constexpr bool operator==(const base&) const = default;
};

struct derived : base {
    constexpr derived() : base(1) {}
};

template <base B>
struct spec {
    static constexpr int value = B.v;
};

inline constexpr derived d{};
inline constexpr base b{1};

#if VARIANT == 'A'
// Is the derived value accepted, with slicing?
static_assert(spec<d>::value == 1);
#elif VARIANT == 'B'
// Is the sliced argument the same specialization as the base value?
static_assert(std::is_same_v<spec<d>, spec<b>>);
#endif

int main() { return 0; }
