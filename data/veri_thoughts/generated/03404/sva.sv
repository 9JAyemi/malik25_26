module binary_to_bcd_sva (
    input logic clk,
    input logic [3:0] BIN,
    input logic [3:0] BCD_HI,
    input logic [3:0] BCD_LO
);

    // BCD_HI is zero-extended from a 2-bit slice.
    check_bcd_hi_zero_extended: assert property (
        @(posedge clk) disable iff (1'b0)
        BCD_HI[3:2] == 2'b00
    );

    // BCD_LO is zero-extended from a 2-bit slice.
    check_bcd_lo_zero_extended: assert property (
        @(posedge clk) disable iff (1'b0)
        BCD_LO[3:2] == 2'b00
    );

    // The output slices reconstruct the computed 4-bit transformed value.
    check_output_matches_combinational_transform: assert property (
        @(posedge clk) disable iff (1'b0)
        {BCD_HI[1:0], BCD_LO[1:0]} ==
        ((BIN + 4'd14) + (((BIN + 4'd14) >= 5'd10) ? 3'd6 : 3'd0))
    );

    // The reconstructed output remains in the 0 to 9 range.
    check_output_within_decimal_range: assert property (
        @(posedge clk) disable iff (1'b0)
        {BCD_HI[1:0], BCD_LO[1:0]} <= 4'd9
    );

    // BIN values 2 through 11 map to BIN minus 2.
    check_midrange_mapping: assert property (
        @(posedge clk) disable iff (1'b0)
        ((BIN >= 4'd2) && (BIN <= 4'd11)) |-> ({BCD_HI[1:0], BCD_LO[1:0]} == (BIN - 4'd2))
    );

    // BIN values 0 and 1 wrap to output values 4 and 5.
    check_low_end_wrap_mapping: assert property (
        @(posedge clk) disable iff (1'b0)
        (BIN <= 4'd1) |-> ({BCD_HI[1:0], BCD_LO[1:0]} == (BIN + 4'd4))
    );

    // BIN values 12 through 15 wrap to output values 0 through 3.
    check_high_end_wrap_mapping: assert property (
        @(posedge clk) disable iff (1'b0)
        (BIN >= 4'd12) |-> ({BCD_HI[1:0], BCD_LO[1:0]} == (BIN - 4'd12))
    );

endmodule