// probes/library/callable_state.cpp                                  -*-C++-*-
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
// A stateful callable handed to an instance member as an lvalue. Each line
// prints how many calls the member made and how many the caller's object
// saw. A member that copies the callable runs the copy, so the caller's
// count stays behind and nothing reports it.

#include <beman/transpose/transpose.hpp>

#include <array>
#include <cstdio>
#include <expected>
#include <optional>
#include <string>
#include <vector>

namespace bt = beman::transpose;

struct counting {
    int calls = 0;
    auto operator()(int x) -> int {
        ++calls;
        return x;
    }
};

struct counting_opt {
    int calls = 0;
    auto operator()(int x) -> std::optional<int> {
        ++calls;
        return x;
    }
};

void report(const char *name, int made, int seen) {
    std::printf("  %-24s calls=%d seen by caller=%d\n", name, made, seen);
}

int main() {
    using opt = std::optional<int>;
    using exp_t = std::expected<int, std::string>;
    {
        counting f;
        (void)bt::applicative<opt>.invoke(f, opt{1});
        report("optional invoke", 1, f.calls);
    }
    {
        counting f;
        (void)bt::applicative<exp_t>.invoke(f, exp_t{1});
        report("expected invoke", 1, f.calls);
    }
    {
        counting f;
        (void)bt::accumulating_applicative<exp_t>.invoke(f, exp_t{1});
        report("accumulating invoke", 1, f.calls);
    }
    {
        counting f;
        (void)bt::applicative<std::array<int, 3>>.invoke(
            f, std::array<int, 3>{1, 2, 3});
        report("array invoke", 3, f.calls);
    }
    {
        counting f;
        (void)bt::applicative<bt::zip_list<int>>.invoke(
            f, bt::zip_list<int>{std::vector<int>{1, 2, 3}});
        report("zip_list invoke", 3, f.calls);
    }
    {
        counting f;
        (void)bt::functor<std::vector<int>>.fmap(f, std::vector<int>{1, 2, 3});
        report("vector fmap", 3, f.calls);
    }
    {
        counting f;
        (void)bt::foldable<std::vector<int>>.any_of(std::vector<int>{0, 0, 0},
                                                    f);
        report("vector any_of", 3, f.calls);
    }
    {
        counting_opt f;
        (void)bt::traverse(f, std::vector<int>{1, 2, 3});
        report("traverse", 3, f.calls);
    }
    {
        counting_opt f;
        (void)bt::monad<opt>.bind(opt{1}, f);
        report("optional bind", 1, f.calls);
    }
}
