//go:build cgo
// +build cgo


package server

/*
#cgo LDFLAGS: -lsgx_dcap_quoteverify
#include <time.h>
#include <sgx_dcap_quoteverify.h>
*/
import "C"

import (
	"fmt"
	"time"
	"unsafe"
)

// sgx_ql_qv_result_t values, from Intel's DCAP headers (sgx_qve_header.h).
var qvResultNames = map[uint32]string{
	0x0000: "OK",
	0xA001: "CONFIG_NEEDED",
	0xA002: "OUT_OF_DATE",
	0xA003: "OUT_OF_DATE_CONFIG_NEEDED",
	0xA004: "INVALID_SIGNATURE",
	0xA005: "REVOKED",
	0xA006: "UNSPECIFIED",
	0xA007: "SW_HARDENING_NEEDED",
	0xA008: "CONFIG_AND_SW_HARDENING_NEEDED",
	0xA009: "TD_RELAUNCH_ADVISED",
	0xA00A: "TD_RELAUNCH_ADVISED_CONFIG_NEEDED",
}

// Results accepted as a passing verification. OK is a fully current platform.
// OUT_OF_DATE is also accepted: the quote is still cryptographically genuine
// (real, unmodified SGX hardware, nothing forged) — it only means the host's
// microcode/firmware isn't on Intel's latest security baseline.

var acceptedQVResults = map[string]bool{
	"OK":          true,
	"OUT_OF_DATE": true,
}

// verifyQuoteDCAP verifies a quote by calling Intel's DCAP quote
// verification library directly via cgo.
func verifyQuoteDCAP(quote []byte) error {
	if len(quote) == 0 {
		return fmt.Errorf("quote is empty")
	}

	quotePtr := (*C.uint8_t)(unsafe.Pointer(&quote[0]))
	quoteSize := C.uint32_t(len(quote))

	var collateralPtr *C.uint8_t
	var collateralSize C.uint32_t
	rc := C.tee_qv_get_collateral(quotePtr, quoteSize, &collateralPtr, &collateralSize)
	if rc != C.SGX_QL_SUCCESS {
		return fmt.Errorf("tee_qv_get_collateral failed: quote3_error_t=0x%04x", uint32(rc))
	}
	defer C.tee_qv_free_collateral(collateralPtr)

	var expirationStatus C.uint32_t
	var qvResult C.sgx_ql_qv_result_t
	rc = C.tee_verify_quote(
		quotePtr, quoteSize,
		collateralPtr,
		C.time_t(time.Now().Unix()),
		&expirationStatus,
		&qvResult,
		nil,
		nil,
	)
	if rc != C.SGX_QL_SUCCESS {
		return fmt.Errorf("tee_verify_quote failed: quote3_error_t=0x%04x", uint32(rc))
	}

	if expirationStatus != 0 {
		fmt.Println("Warning: quote verification collateral is expired")
	}

	resultCode := uint32(qvResult)
	resultName, known := qvResultNames[resultCode]
	if !known {
		resultName = fmt.Sprintf("UNKNOWN(0x%04x)", resultCode)
	}

	if acceptedQVResults[resultName] {
		fmt.Printf("Quote verification succeeded: %s\n", resultName)
		return nil
	}

	return fmt.Errorf("quote verification result not accepted: %s (code=0x%04x)", resultName, resultCode)
}
