module signed_mag_to_twos_comp_sva (
    input logic clk,
    input  signed [15:0] signed_mag,
    input  signed [15:0] twos_comp
);
    // Output equals input (combinational pass-through).
    check_output_equals_input: assert property (
        @(posedge clk) (twos_comp == signed_mag)
    );

    // Sign bits match between input and output.
    check_sign_bit_match: assert property (
        @(posedge clk) (twos_comp[15] == signed_mag[15])
    );

    // If input is non-negative, output equals input.
    check_nonneg_passthrough: assert property (
        @(posedge clk) (signed_mag >= 0) |-> (twos_comp == signed_mag)
    );

    // If input is negative, output equals input.
    check_neg_passthrough: assert property (
        @(posedge clk) (signed_mag < 0) |-> (twos_comp == signed_mag)
    );

    // Stable input across cycles implies stable output.
    check_stable_propagation: assert property (
        @(posedge clk) $stable(signed_mag) |-> $stable(twos_comp)
    );

    // Any input change across cycles implies output changes.
    check_change_propagation: assert property (
        @(posedge clk) $changed(signed_mag) |-> $changed(twos_comp)
    );

    // Zero input passes through as zero.
    check_zero_passthrough: assert property (
        @(posedge clk) (signed_mag == 16'sd0) |-> (twos_comp == 16'sd0)
    );

    // Minimum value (0x8000) passes through unchanged.
    check_min_int_passthrough: assert property (
        @(posedge clk) (signed_mag == 16'sh8000) |-> (twos_comp == 16'sh8000)
    );

    // Maximum value (0x7FFF) passes through unchanged.
    check_max_int_passthrough: assert property (
        @(posedge clk) (signed_mag == 16'sh7FFF) |-> (twos_comp == 16'sh7FFF)
    );

    // Output bits match input bits (bitwise equality).
    check_bitwise_equality: assert property (
        @(posedge clk) (twos_comp ^ signed_mag) == 16'sd0
    );
endmodule