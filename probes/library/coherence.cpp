// probes/library/coherence.cpp                                       -*-C++-*-
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
// An algorithm handed an applicative object must take every operation on
// that context from the object. std::expected has two: the canonical
// short-circuit object and the accumulating one. Each line prints whether a
// result built from two failures (alpha and beta) still holds each. The
// honest algorithm and the library's derived members should hold both under
// the accumulating object; a slip through an operation object, which looks
// up the canonical instance, or through bind, holds only the first, and
// compiles without complaint.

#include <beman/transpose/transpose.hpp>

#include <cstdio>
#include <expected>
#include <functional>
#include <vector>

namespace bt = beman::transpose;

namespace coherence_probe {
struct alpha {
    int value{};
    friend auto operator==(const alpha &, const alpha &) -> bool = default;
};
struct beta {
    int value{};
    friend auto operator==(const beta &, const beta &) -> bool = default;
};
} // namespace coherence_probe

using coherence_probe::alpha;
using coherence_probe::beta;
using mixed = bt::error_set<alpha, beta>;
using E = std::expected<int, mixed>;

auto fails_alpha() -> E { return E{std::unexpect, alpha{1}}; }
auto fails_beta() -> E { return E{std::unexpect, beta{2}}; }

template <class APP>
auto add_honest(const APP &app, const E &a, const E &b) -> E {
    return app.invoke(std::plus<>{}, a, b);
}

template <class APP>
auto add_slip_operation(const APP &, const E &a, const E &b) -> E {
    return bt::invoke(std::plus<>{}, a, b);
}

template <class APP>
auto add_slip_bind(const APP &app, const E &a, const E &b) -> E {
    return bt::bind(a, [&](int x) {
        return bt::bind(b, [&](int y) { return app.pure(x + y); });
    });
}

void report(const char *name, const E &r) {
    std::printf("  %-28s alpha=%d beta=%d\n", name,
                !r.has_value() && r.error().holds<alpha>(),
                !r.has_value() && r.error().holds<beta>());
}

int main() {
    const auto &acc = bt::accumulating_applicative<E>;
    const E a = fails_alpha();
    const E b = fails_beta();

    report("honest invoke", add_honest(acc, a, b));
    report("slip: operation object", add_slip_operation(acc, a, b));
    report("slip: bind", add_slip_bind(acc, a, b));
    report("derived zip_with", acc.zip_with(std::plus<>{}, a, b));
    report("derived discard_first", acc.discard_first(a, b));
    report("derived discard_second", acc.discard_second(a, b));
    report("derived invoke_with", acc.invoke_with(acc, std::plus<>{}, a, b));

    auto classify = [](int x) -> E {
        return x == 0 ? fails_alpha() : x == 1 ? fails_beta() : E{x};
    };
    report("traverse, policy given",
           bt::traverse(classify, std::vector<int>{0, 1, 2}, acc)
               .transform([](auto &&) { return 0; }));
    report("traverse, policy omitted",
           bt::traverse(classify, std::vector<int>{0, 1, 2})
               .transform([](auto &&) { return 0; }));
}
