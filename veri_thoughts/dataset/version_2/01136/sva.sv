module BCD_to_Binary_sva (
    input logic CLK,
    input logic [3:0] bcd,
    input logic [7:0] bin
);
    // DUT has no clock or reset; combinational logic only. Assertions are sampled on external CLK.
    // Structure: bin = {zero-extended LUT[bcd[1:0]], zero-extended LUT[bcd]} ⇒ only bin[4] and bin[0] can be 1.

    // Past-valid guard for $past/$stable/$changed usage.
    logic past_valid;
    always_ff @(posedge CLK) past_valid <= 1'b1;

    // High nibble must have only its LSB possibly set.
    check_high_nibble_shape: assert property (
        @(posedge CLK) bin[7:4] == {3'b000, bin[4]}
    );

    // Low nibble must have only its LSB possibly set.
    check_low_nibble_shape: assert property (
        @(posedge CLK) bin[3:0] == {3'b000, bin[0]}
    );

    // No ones outside bit positions 4 and 0.
    check_reserved_bits_zero: assert property (
        @(posedge CLK) (bin & 8'hEE) == 8'h00
    );

    // If BCD input is stable, BIN output must be stable (purely combinational behavior).
    check_deterministic_function: assert property (
        @(posedge CLK) past_valid && $stable(bcd) |-> $stable(bin)
    );

    // If low two bits of BCD are stable, bin[4] must be stable (bin[4] depends only on bcd[1:0]).
    check_bin4_stable_with_low2_stable: assert property (
        @(posedge CLK) past_valid && $stable(bcd[1:0]) |-> $stable(bin[4])
    );

    // A change on bin[4] implies a change on bcd[1:0].
    check_bin4_change_implies_low2_change: assert property (
        @(posedge CLK) past_valid && $changed(bin[4]) |-> !$stable(bcd[1:0])
    );

    // A change on bin[0] implies some bit of bcd changed.
    check_bin0_change_implies_bcd_change: assert property (
        @(posedge CLK) past_valid && $changed(bin[0]) |-> !$stable(bcd)
    );

    // If only upper two bits of BCD change, the high nibble must remain stable.
    check_high_nibble_independent_of_upper_bcd: assert property (
        @(posedge CLK) past_valid && $stable(bcd[1:0]) |-> $stable(bin[7:4])
    );

endmodule