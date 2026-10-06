package vm

import "math"

// Value kinds used by OpConvert.
const (
	KindInt  = 0
	KindUint = 1
	KindF64  = 2
	KindF32  = 3
)

// MakeConvertOperand packs a conversion descriptor into the operand of
// OpConvert. fromBits and toBits are the bit widths of the source and target
// types (8, 16, 32 or 64 for integers; 32 or 64 for floats).
func MakeConvertOperand(fromKind, fromBits, toKind, toBits int) int64 {
	return int64(fromKind) |
		int64(fromBits)<<8 |
		int64(toKind)<<16 |
		int64(toBits)<<24
}

// UnpackConvertOperand is the inverse of MakeConvertOperand.
func UnpackConvertOperand(op int64) (fromKind, fromBits, toKind, toBits int) {
	return int(op & 0xff),
		int((op >> 8) & 0xff),
		int((op >> 16) & 0xff),
		int((op >> 24) & 0xff)
}

// signExtend widens the low bits of v to a signed 64-bit integer.
func signExtend(v uint64, bits int) int64 {
	if bits >= 64 {
		return int64(v)
	}
	shift := uint(64 - bits)
	return int64(v<<shift) >> shift
}

// zeroExtend clears every bit of v above the low bits.
func zeroExtend(v uint64, bits int) uint64 {
	if bits >= 64 {
		return v
	}
	return v & (1<<uint(bits) - 1)
}

// Convert applies the conversion described by operand to the word v.
//
// The conversion set is exactly Go's numeric conversion set for the types the
// virtual machine supports: integer to integer (truncating then sign- or
// zero-extending according to the target), integer to float, float to integer
// and float32 <-> float64.
//
// Go leaves out-of-range float to integer conversions implementation-defined.
// The VM inherits the host Go conversion, so the interpreter and the emitted
// program agree by construction: both execute the same Go expression on the
// same platform. This is documented in docs/VIRTUALIZATION.md.
func Convert(v uint64, operand int64) uint64 {
	fromKind, fromBits, toKind, toBits := UnpackConvertOperand(operand)

	switch toKind {
	case KindInt, KindUint:
		var i int64
		switch fromKind {
		case KindInt:
			i = signExtend(v, fromBits)
		case KindUint:
			i = int64(zeroExtend(v, fromBits))
		case KindF64:
			i = int64(math.Float64frombits(v))
		case KindF32:
			i = int64(math.Float32frombits(uint32(v)))
		default:
			panic("vm: invalid source kind in conversion")
		}
		if toKind == KindUint {
			return zeroExtend(uint64(i), toBits)
		}
		return uint64(signExtend(uint64(i), toBits))

	case KindF64:
		var f float64
		switch fromKind {
		case KindInt:
			f = float64(signExtend(v, fromBits))
		case KindUint:
			f = float64(zeroExtend(v, fromBits))
		case KindF64:
			f = math.Float64frombits(v)
		case KindF32:
			f = float64(math.Float32frombits(uint32(v)))
		default:
			panic("vm: invalid source kind in conversion")
		}
		return math.Float64bits(f)

	case KindF32:
		var f float32
		switch fromKind {
		case KindInt:
			f = float32(signExtend(v, fromBits))
		case KindUint:
			f = float32(zeroExtend(v, fromBits))
		case KindF64:
			f = float32(math.Float64frombits(v))
		case KindF32:
			f = math.Float32frombits(uint32(v))
		default:
			panic("vm: invalid source kind in conversion")
		}
		return uint64(math.Float32bits(f))
	}
	panic("vm: invalid target kind in conversion")
}
