module top_module_sva (
    input logic [7:0] binary,
    input logic [7:0] excess128,
    input logic       result
);
    // No clock/reset in RTL; pure combinational; assertions use $global_clock.

    ///// binary_to_excess128 mapping /////
    // excess128 equals binary + 8'd128 (mod 256).
    check_excess128_addition: assert property (
        @($global_clock) (excess128 == (binary + 8'd128))
    );

    // Lower 7 bits are unchanged by +128.
    check_excess128_lower_bits_unchanged: assert property (
        @($global_clock) (excess128[6:0] == binary[6:0])
    );

    // MSB is toggled by +128.
    check_excess128_msb_toggled: assert property (
        @($global_clock) (excess128[7] == ~binary[7])
    );

    // Only MSB differs between binary and excess128.
    check_excess128_xor_mask: assert property (
        @($global_clock) ((excess128 ^ binary) == 8'h80)
    );

    // Modular difference is 128.
    check_excess128_minus_binary_128: assert property (
        @($global_clock) ((excess128 - binary) == 8'd128)
    );

    // Adding 128 to excess128 returns binary.
    check_inverse_addition: assert property (
        @($global_clock) (binary == (excess128 + 8'd128))
    );

    ///// compare_binary_excess128 behavior /////
    // result reflects equality of binary and excess128.
    check_compare_function: assert property (
        @($global_clock) (result == (binary == excess128))
    );

    ///// Top-level composition /////
    // Given the mapping, binary and excess128 are never equal.
    check_never_equal: assert property (
        @($global_clock) (binary != excess128)
    );

    // Therefore result is always 0.
    check_result_always_zero: assert property (
        @($global_clock) (result == 1'b0)
    );
endmodule