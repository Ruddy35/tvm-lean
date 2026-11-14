// Stand-in for the TL-generated API header that crypto/block/signature-set.h includes (block.h,
// mc-config.h, tonops.cpp): the build compiles no code that uses these types (block.cpp and
// signature-set.cpp are left out, build.sh), so declarations are enough.
#pragma once
#include "tl/TlObject.h"

namespace ton {
namespace lite_api {
class liteServer_SignatureSet;
}  // namespace lite_api
namespace ton_api {
class tonNode_SignatureSet;
class tonNode_blockSignature;
class consensus_CandidateHashData;
}  // namespace ton_api
}  // namespace ton
