// Copyright 2014 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// The go-ethereum library is free software: you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// The go-ethereum library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with the go-ethereum library. If not, see <http://www.gnu.org/licenses/>.

package types

import (
	"math/big"
	"sync/atomic"
	"time"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/common/math"
	"github.com/ethereum/go-ethereum/rlp"
)

// Transaction is an Ethereum transaction.
type TransactionBase struct {
	inner TxDataBase // Consensus contents of a transaction
	time  time.Time  // Time first seen locally (spam avoidance)

	// caches
	hash atomic.Value
	size atomic.Value
	from atomic.Value
}

// NewTx creates a new transaction.
func NewTxBase(inner TxData) *TransactionBase {
	tx := new(TransactionBase)
	tx.setDecoded(inner.copy(), 0)
	return tx
}

// TxData is the underlying data of a transaction.
//
// This is implemented by DynamicFeeTx, LegacyTx and AccessListTx.
type TxDataBase interface {
	txType() byte // returns the type ID
	copy() TxData // creates a deep copy and initializes all fields

	chainID() *big.Int
	accessList() AccessList
	data() []byte
	gas() uint64
	gasPrice() *big.Int
	gasTipCap() *big.Int
	gasFeeCap() *big.Int
	value() *big.Int
	nonce() uint64
	to() *common.Address

	rawSignatureValues() (v, r, s *big.Int)
	setSignatureValues(chainID, v, r, s *big.Int)

	// effectiveGasPrice computes the gas price paid by the transaction, given
	// the inclusion block baseFee.
	//
	// Unlike other TxData methods, the returned *big.Int should be an independent
	// copy of the computed value, i.e. callers are allowed to mutate the result.
	// Method implementations can use 'dst' to store the result.
	//effectiveGasPrice(dst *big.Int, baseFee *big.Int) *big.Int

	//encode(*bytes.Buffer) error
	//decode([]byte) error
}

// DecodeRLP implements rlp.Decoder
func (tx *TransactionBase) DecodeRLP(s *rlp.Stream) error {
	kind, size, err := s.Kind()
	switch {
	case err != nil:
		return err
	case kind == rlp.List:
		// It's a legacy transaction.
		var inner LegacyTx
		err := s.Decode(&inner)
		if err == nil {
			tx.setDecoded(&inner, rlp.ListSize(size))
		}
		return err
	case kind == rlp.Byte:
		return errShortTypedTx
	default:
		// It's an EIP-2718 typed TX envelope.
		// First read the tx payload bytes into a temporary buffer.
		b, buf, err := getPooledBuffer(size)
		if err != nil {
			return err
		}
		defer encodeBufferPool.Put(buf)
		if err := s.ReadBytes(b); err != nil {
			return err
		}
		// Now decode the inner transaction.
		inner, err := tx.decodeTyped(b)
		if err == nil {
			tx.setDecoded(inner, size)
		}
		return err
	}
}

// UnmarshalBinary decodes the canonical encoding of transactions.
// It supports legacy RLP transactions and EIP-2718 typed transactions.
func (tx *TransactionBase) UnmarshalBinary(b []byte) error {
	if len(b) > 0 && b[0] > 0x7f {
		// It's a legacy transaction.
		var data LegacyTx
		err := rlp.DecodeBytes(b, &data)
		if err != nil {
			return err
		}
		tx.setDecoded(&data, uint64(len(b)))
		return nil
	}
	// It's an EIP-2718 typed transaction envelope.
	inner, err := tx.decodeTyped(b)
	if err != nil {
		return err
	}
	tx.setDecoded(inner, uint64(len(b)))
	return nil
}

// decodeTyped decodes a typed transaction from the canonical format.
func (tx *TransactionBase) decodeTyped(b []byte) (TxData, error) {
	if len(b) <= 1 {
		return nil, errShortTypedTx
	}
	var inner TxData
	switch b[0] {
	case AccessListTxType:
		inner = new(AccessListTx)
	case DynamicFeeTxType:
		inner = new(DynamicFeeTx)
	case BlobTxType:
		inner = new(BlobTx)
	default:
		return nil, ErrTxTypeNotSupported
	}
	err := inner.decode(b[1:])
	return inner, err
}

// setDecoded sets the inner transaction and size after decoding.
func (tx *TransactionBase) setDecoded(inner TxData, size uint64) {
	tx.inner = inner
	tx.time = time.Now()
	if size > 0 {
		tx.size.Store(size)
	}
}

// Protected says whether the transaction is replay-protected.
func (tx *TransactionBase) Protected() bool {
	switch tx := tx.inner.(type) {
	case *LegacyTx:
		return tx.V != nil && isProtectedV(tx.V)
	default:
		return true
	}
}

// Type returns the transaction type.
func (tx *TransactionBase) Type() uint8 {
	return tx.inner.txType()
}

// ChainId returns the EIP155 chain ID of the transaction. The return value will always be
// non-nil. For legacy transactions which are not replay-protected, the return value is
// zero.
func (tx *TransactionBase) ChainId() *big.Int {
	return tx.inner.chainID()
}

// Data returns the input data of the transaction.
func (tx *TransactionBase) Data() []byte { return tx.inner.data() }

// AccessList returns the access list of the transaction.
func (tx *TransactionBase) AccessList() AccessList { return tx.inner.accessList() }

// Gas returns the gas limit of the transaction.
func (tx *TransactionBase) Gas() uint64 { return tx.inner.gas() }

// GasPrice returns the gas price of the transaction.
func (tx *TransactionBase) GasPrice() *big.Int { return new(big.Int).Set(tx.inner.gasPrice()) }

// GasTipCap returns the gasTipCap per gas of the transaction.
func (tx *TransactionBase) GasTipCap() *big.Int { return new(big.Int).Set(tx.inner.gasTipCap()) }

// GasFeeCap returns the fee cap per gas of the transaction.
func (tx *TransactionBase) GasFeeCap() *big.Int { return new(big.Int).Set(tx.inner.gasFeeCap()) }

// Value returns the ether amount of the transaction.
func (tx *TransactionBase) Value() *big.Int { return new(big.Int).Set(tx.inner.value()) }

// Nonce returns the sender account nonce of the transaction.
func (tx *TransactionBase) Nonce() uint64 { return tx.inner.nonce() }

// To returns the recipient address of the transaction.
// For contract-creation transactions, To returns nil.
func (tx *TransactionBase) To() *common.Address {
	return copyAddressPtr(tx.inner.to())
}

// Cost returns (gas * gasPrice) + (blobGas * blobGasPrice) + value.
func (tx *TransactionBase) Cost() *big.Int {
	total := new(big.Int).Mul(tx.GasPrice(), new(big.Int).SetUint64(tx.Gas()))
	if tx.Type() == BlobTxType {
		total.Add(total, new(big.Int).Mul(tx.BlobGasFeeCap(), new(big.Int).SetUint64(tx.BlobGas())))
	}
	total.Add(total, tx.Value())
	return total
}

// RawSignatureValues returns the V, R, S signature values of the transaction.
// The return values should not be modified by the caller.
func (tx *TransactionBase) RawSignatureValues() (v, r, s *big.Int) {
	return tx.inner.rawSignatureValues()
}

// GasFeeCapCmp compares the fee cap of two transactions.
func (tx *TransactionBase) GasFeeCapCmp(other *TransactionBase) int {
	return tx.inner.gasFeeCap().Cmp(other.inner.gasFeeCap())
}

// GasFeeCapIntCmp compares the fee cap of the transaction against the given fee cap.
func (tx *TransactionBase) GasFeeCapIntCmp(other *big.Int) int {
	return tx.inner.gasFeeCap().Cmp(other)
}

// GasTipCapCmp compares the gasTipCap of two transactions.
func (tx *TransactionBase) GasTipCapCmp(other *TransactionBase) int {
	return tx.inner.gasTipCap().Cmp(other.inner.gasTipCap())
}

// GasTipCapIntCmp compares the gasTipCap of the transaction against the given gasTipCap.
func (tx *TransactionBase) GasTipCapIntCmp(other *big.Int) int {
	return tx.inner.gasTipCap().Cmp(other)
}

// EffectiveGasTip returns the effective miner gasTipCap for the given base fee.
// Note: if the effective gasTipCap is negative, this method returns both error
// the actual negative value, _and_ ErrGasFeeCapTooLow
func (tx *TransactionBase) EffectiveGasTip(baseFee *big.Int) (*big.Int, error) {
	if baseFee == nil {
		return tx.GasTipCap(), nil
	}
	var err error
	gasFeeCap := tx.GasFeeCap()
	if gasFeeCap.Cmp(baseFee) == -1 {
		err = ErrGasFeeCapTooLow
	}
	return math.BigMin(tx.GasTipCap(), gasFeeCap.Sub(gasFeeCap, baseFee)), err
}

// EffectiveGasTipValue is identical to EffectiveGasTip, but does not return an
// error in case the effective gasTipCap is negative
func (tx *TransactionBase) EffectiveGasTipValue(baseFee *big.Int) *big.Int {
	effectiveTip, _ := tx.EffectiveGasTip(baseFee)
	return effectiveTip
}

// EffectiveGasTipCmp compares the effective gasTipCap of two transactions assuming the given base fee.
func (tx *TransactionBase) EffectiveGasTipCmp(other *TransactionBase, baseFee *big.Int) int {
	if baseFee == nil {
		return tx.GasTipCapCmp(other)
	}
	return tx.EffectiveGasTipValue(baseFee).Cmp(other.EffectiveGasTipValue(baseFee))
}

// EffectiveGasTipIntCmp compares the effective gasTipCap of a transaction to the given gasTipCap.
func (tx *TransactionBase) EffectiveGasTipIntCmp(other *big.Int, baseFee *big.Int) int {
	if baseFee == nil {
		return tx.GasTipCapIntCmp(other)
	}
	return tx.EffectiveGasTipValue(baseFee).Cmp(other)
}

// BlobGas returns the blob gas limit of the transaction for blob transactions, 0 otherwise.
func (tx *TransactionBase) BlobGas() uint64 {
	if blobtx, ok := tx.inner.(*BlobTx); ok {
		return blobtx.blobGas()
	}
	return 0
}

// BlobGasFeeCap returns the blob gas fee cap per blob gas of the transaction for blob transactions, nil otherwise.
func (tx *TransactionBase) BlobGasFeeCap() *big.Int {
	if blobtx, ok := tx.inner.(*BlobTx); ok {
		return blobtx.BlobFeeCap.ToBig()
	}
	return nil
}

// BlobHashes returns the hashes of the blob commitments for blob transactions, nil otherwise.
func (tx *TransactionBase) BlobHashes() []common.Hash {
	if blobtx, ok := tx.inner.(*BlobTx); ok {
		return blobtx.BlobHashes
	}
	return nil
}

// BlobTxSidecar returns the sidecar of a blob transaction, nil otherwise.
func (tx *TransactionBase) BlobTxSidecar() *BlobTxSidecar {
	if blobtx, ok := tx.inner.(*BlobTx); ok {
		return blobtx.Sidecar
	}
	return nil
}

// BlobGasFeeCapCmp compares the blob fee cap of two transactions.
func (tx *TransactionBase) BlobGasFeeCapCmp(other *TransactionBase) int {
	return tx.BlobGasFeeCap().Cmp(other.BlobGasFeeCap())
}

// BlobGasFeeCapIntCmp compares the blob fee cap of the transaction against the given blob fee cap.
func (tx *TransactionBase) BlobGasFeeCapIntCmp(other *big.Int) int {
	return tx.BlobGasFeeCap().Cmp(other)
}

// WithoutBlobTxSidecar returns a copy of tx with the blob sidecar removed.
func (tx *TransactionBase) WithoutBlobTxSidecar() *TransactionBase {
	blobtx, ok := tx.inner.(*BlobTx)
	if !ok {
		return tx
	}
	cpy := &TransactionBase{
		inner: blobtx.withoutSidecar(),
		time:  tx.time,
	}
	// Note: tx.size cache not carried over because the sidecar is included in size!
	if h := tx.hash.Load(); h != nil {
		cpy.hash.Store(h)
	}
	if f := tx.from.Load(); f != nil {
		cpy.from.Store(f)
	}
	return cpy
}

// SetTime sets the decoding time of a transaction. This is used by tests to set
// arbitrary times and by persistent transaction pools when loading old txs from
// disk.
func (tx *TransactionBase) SetTime(t time.Time) {
	tx.time = t
}

// Time returns the time when the transaction was first seen on the network. It
// is a heuristic to prefer mining older txs vs new all other things equal.
func (tx *TransactionBase) Time() time.Time {
	return tx.time
}

// Hash returns the transaction hash.
func (tx *TransactionBase) Hash() common.Hash {
	if hash := tx.hash.Load(); hash != nil {
		return hash.(common.Hash)
	}

	var h common.Hash
	if tx.Type() == LegacyTxType {
		h = rlpHash(tx.inner)
	} else {
		h = prefixedRlpHash(tx.Type(), tx.inner)
	}
	tx.hash.Store(h)
	return h
}

// Size returns the true encoded storage size of the transaction, either by encoding
// and returning it, or returning a previously cached value.
func (tx *TransactionBase) Size() uint64 {
	if size := tx.size.Load(); size != nil {
		return size.(uint64)
	}

	// Cache miss, encode and cache.
	// Note we rely on the assumption that all tx.inner values are RLP-encoded!
	c := writeCounter(0)
	rlp.Encode(&c, &tx.inner)
	size := uint64(c)

	// For blob transactions, add the size of the blob content and the outer list of the
	// tx + sidecar encoding.
	if sc := tx.BlobTxSidecar(); sc != nil {
		size += rlp.ListSize(sc.encodedSize())
	}

	// For typed transactions, the encoding also includes the leading type byte.
	if tx.Type() != LegacyTxType {
		size += 1
	}

	tx.size.Store(size)
	return size
}

// Transactions implements DerivableList for transactions.
type TransactionsBase []*TransactionBase

// Len returns the length of s.
func (s TransactionsBase) Len() int { return len(s) }

// TxByNonce implements the sort interface to allow sorting a list of transactions
// by their nonces. This is usually only useful for sorting transactions from a
// single account, otherwise a nonce comparison doesn't make much sense.
type TxByNonceBase TransactionsBase

func (s TxByNonceBase) Len() int           { return len(s) }
func (s TxByNonceBase) Less(i, j int) bool { return s[i].Nonce() < s[j].Nonce() }
func (s TxByNonceBase) Swap(i, j int)      { s[i], s[j] = s[j], s[i] }
