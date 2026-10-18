// probes/library/state.cpp                                           -*-C++-*-
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
// An algorithm that takes an instance's type and makes a fresh object of it
// assumes the instance carries no state. The first table asks which of the
// library's own instance objects that assumption would admit: empty, and
// default-initializable. The last lines pass a stateful applicative object
// to lifted_monoid, which makes its own, and to traverse, which takes the
// object passed.

#include <beman/transpose/induced_monoid.hpp>
#include <beman/transpose/transpose.hpp>

#include <array>
#include <concepts>
#include <cstdio>
#include <expected>
#include <optional>
#include <string>
#include <type_traits>
#include <vector>

namespace bt = beman::transpose;

using opt = std::optional<int>;
using vec = std::vector<int>;
using exp_t = std::expected<int, std::string>;

template <class T>
void row(const char *name) {
    std::printf("  %-44s empty=%d default=%d\n", name, std::is_empty_v<T>,
                std::default_initializable<T>);
}

#define ROW(...) row<std::remove_cvref_t<decltype(__VA_ARGS__)>>(#__VA_ARGS__)
#define ROWT(...) row<__VA_ARGS__>(#__VA_ARGS__)

using app_opt_t = std::remove_cvref_t<decltype(bt::applicative<opt>)>;

struct logging_app {
    std::vector<const char *> *log = nullptr;
    void note(const char *what) const {
        if (log != nullptr) {
            log->push_back(what);
        }
    }
    auto pure(int x) const -> opt {
        note("pure");
        return x;
    }
    template <class F>
    auto invoke(F &&f, const opt &a, const opt &b) const -> opt {
        note("invoke");
        if (a && b) {
            return f(*a, *b);
        }
        return {};
    }
};

int main() {
    ROW(bt::applicative<opt>);
    ROW(bt::applicative<exp_t>);
    ROW(bt::accumulating_applicative<exp_t>);
    ROW(bt::applicative<std::array<int, 3>>);
    ROW(bt::applicative<bt::zip_list<int>>);
    ROW(bt::applicative<bt::sender<int>>);
    ROW(bt::monad<opt>);
    ROW(bt::monad<exp_t>);
    ROW(bt::functor<opt>);
    ROW(bt::foldable<vec>);
    ROW(bt::traversable<vec>);
    ROWT(bt::Monoid<std::string>);
    ROWT(bt::sum_monoid<int>);
    ROWT(bt::lifted_monoid<app_opt_t, opt, bt::sum_monoid<int>>);

    std::vector<const char *> log;
    const logging_app mine{&log};
    bt::lifted_monoid<logging_app, opt, bt::sum_monoid<int>> lifted;
    auto sum = lifted.combine(opt{1}, opt{2});
    std::printf("  lifted_monoid<logging_app>: sum=%d, calls logged=%zu\n",
                sum.value_or(-1), log.size());
    (void)mine;
}
