// Stand-in for the TL-generated API header that keys/encryptor.h includes (crypto/block/
// validator-set.h, mc-config.h, tonops.cpp): the build compiles no code that uses these types
// (block.cpp, signature-set.cpp and the keys library are left out, build.sh), so declarations are
// enough.
#pragma once
#include "auto/tl/lite_api.hpp"
