import TvmLean.Model.Host.Host

namespace TvmLean

def stubHost : Host where
  blsVerify := fun _ _ _ => false
  blsAggregate := fun _ => ByteArray.mk #[]
  blsFastAggregateVerify := fun _ _ _ => false
  blsAggregateVerify := fun _ _ _ => false
  blsG1AddBytes := fun _ _ => ByteArray.mk #[]
  blsG1SubBytes := fun _ _ => ByteArray.mk #[]
  blsG1NegBytes := fun _ => ByteArray.mk #[]
  blsG1MulBytes := fun _ _ => ByteArray.mk #[]
  blsG1MultiExpBytes := fun _ _ => ByteArray.mk #[]
  blsG1ZeroBytes := fun _ => ByteArray.mk #[]
  blsMapToG1Bytes := fun _ => ByteArray.mk #[]
  blsG1InGroup := fun _ => false
  blsG1IsZero := fun _ => false
  blsG2AddBytes := fun _ _ => ByteArray.mk #[]
  blsG2SubBytes := fun _ _ => ByteArray.mk #[]
  blsG2NegBytes := fun _ => ByteArray.mk #[]
  blsG2MulBytes := fun _ _ => ByteArray.mk #[]
  blsG2MultiExpBytes := fun _ _ => ByteArray.mk #[]
  blsG2ZeroBytes := fun _ => ByteArray.mk #[]
  blsMapToG2Bytes := fun _ => ByteArray.mk #[]
  blsG2InGroup := fun _ => false
  blsG2IsZero := fun _ => false
  blsPairing := fun _ _ => 0

end TvmLean
