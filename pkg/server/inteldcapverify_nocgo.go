//go:build !cgo
// +build !cgo

package server

import "errors"

// verifyQuoteDCAP is a placeholder for erroring with a message if
// the binary has been built with CGO_ENABLED=0.
func verifyQuoteDCAP(quote []byte) error {
	return errors.New("binary has been built with no cgo support, DCAP quote verification not supported")
}
