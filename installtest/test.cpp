// testinstall/test.cpp                                               -*-C++-*-
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

#include <iostream>
#include <smd/overload/encoding.hpp>

int main() {
    std::cout << "draft pin: |" << overload::draft_pin() << '|' << '\n';
    return 0;
}
