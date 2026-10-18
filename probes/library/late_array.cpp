// probes/library/late_array.cpp                                      -*-C++-*-
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
// The std::array Applicative instance is declared in array.hpp, not with the
// typeclass in apply.hpp. A use of the lookup before array.hpp is included
// and a use after it make the program ill-formed, no diagnostic required
// ([temp.spec.partial.general]/1). VARIANT 'P' probes before the include
// only; 'A' also asserts the instance is visible after it; 'C' calls through
// it after it.

#include <beman/transpose/apply.hpp>

#include <array>

namespace bt = beman::transpose;

inline constexpr auto inc = [](int x) { return x + 1; };

template <class C>
constexpr bool can_invoke = requires(C c) { bt::invoke(inc, c); };

static_assert(!can_invoke<std::array<int, 3>>);

#include <beman/transpose/array.hpp>

#if VARIANT == 'A'
static_assert(can_invoke<std::array<int, 3>>);
#elif VARIANT == 'C'
auto r = bt::invoke(inc, std::array<int, 3>{1, 2, 3});
#endif

int main() {}
