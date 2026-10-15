// hello.cpp -*-C++-*-

#include <smd/overload/encoding.hpp>

#include <iostream>
#include <vector>

// A Functor instance for std::vector, declared before any use that would
// instantiate its lookup: the single-tu assumption of the model, in code.
struct vector_functor_impl {
    template <class FUNCTION, class T>
    static auto fmap(FUNCTION &&function, const std::vector<T> &values) {
        std::vector<decltype(function(values.front()))> out;
        out.reserve(values.size());
        for (const auto &value : values) {
            out.push_back(function(value));
        }
        return out;
    }
};

template <class T>
inline constexpr overload::derive_functor<vector_functor_impl>
    overload::functor<std::vector<T>>{};

// 710c39c6-c7e1-403f-a9f0-9f8ecf890dc9
int main() {
    std::vector<int> numbers{1, 2, 3};
    auto doubled = overload::fmap([](int i) { return 2 * i; }, numbers);
    std::cout << "Hello, " << overload::draft_pin() << ':';
    for (int i : doubled) {
        std::cout << ' ' << i;
    }
    std::cout << '\n';
}
// 710c39c6-c7e1-403f-a9f0-9f8ecf890dc9 end
