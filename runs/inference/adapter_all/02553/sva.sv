module binary_multiplier_sva (
    input logic        clk,
    input logic [7:0]  a,
    input logic [7:0]  b,
    input logic [15:0] result
);

    // Result matches the zero-extended product of a and b.
    check_result_matches_product: assert property (
        @(posedge clk) result == ({8'b0, a} * {8'b0, b})
    );

    // Zero on a forces a zero result.
    check_zero_a_forces_zero_result: assert property (
        @(posedge clk) (a == 8'h00) |-> (result == 16'h0000)
    );

    // Zero on b forces a zero result.
    check_zero_b_forces_zero_result: assert property (
        @(posedge clk) (b == 8'h00) |-> (result == 16'h0000)
    );

    // Eight-bit 0xFF on a produces a 16-bit 0xFF00 result.
    check_ff_a_maps_to_ff00: assert property (
        @(posedge clk) (a == 8'hFF) |-> (result == 16'hFF00)
    );

    // Eight-bit 0xFF on b produces a 16-bit 0xFF00 result.
    check_ff_b_maps_to_ff00: assert property (
        @(posedge clk) (b == 8'hFF) |-> (result == 16'hFF00)
    );

    // Eight-bit 0x80 on a produces a 16-bit 0x8000 result.
    check_80_a_maps_to_8000: assert property (
        @(posedge clk) (a == 8'h80) |-> (result == 16'h8000)
    );

    // Eight-bit 0x80 on b produces a 16-bit 0x8000 result.
    check_80_b_maps_to_8000: assert property (
        @(posedge clk) (b == 8'h80) |-> (result == 16'h8000)
    );

    // Eight-bit 0x01 on a passes b through to the result.
    check_one_a_passes_b: assert property (
        @(posedge clk) (a == 8'h01) |-> (result == {8'b0, b})
    );

    // Eight-bit 0x01 on b passes a through to the result.
    check_one_b_passes_a: assert property (
        @(posedge clk) (b == 8'h01) |-> (result == {8'b0, a})
    );

    // Eight-bit 0x02 on a shifts b left by one bit.
    check_two_a_shifts_b_left_one: assert property (
        @(posedge clk) (a == 8'h02) |-> (result == ({8'b0, b} << 1))
    );

    // Eight-bit 0x02 on b shifts a left by one bit.
    check_two_b_shifts_a_left_one: assert property (
        @(posedge clk) (b == 8'h02) |-> (result == ({8'b0, a} << 1))
    );

    // Eight-bit 0x04 on a shifts b left by two bits.
    check_four_a_shifts_b_left_two: assert property (
        @(posedge clk) (a == 8'h04) |-> (result == ({8'b0, b} << 2))
    );

    // Eight-bit 0x04 on b shifts a left by two bits.
    check_four_b_shifts_a_left_two: assert property (
        @(posedge clk) (b == 8'h04) |-> (result == ({8'b0, a} << 2))
    );

    // Eight-bit 0x08 on a shifts b left by three bits.
    check_eight_a_shifts_b_left_three: assert property (
        @(posedge clk) (a == 8'h08) |-> (result == ({8'b0, b} << 3))
    );

    // Eight-bit 0x08 on b shifts a left by three bits.
    check_eight_b_shifts_a_left_three: assert property (
        @(posedge clk) (b == 8'h08) |-> (result == ({8'b0, a} << 3))
    );

endmodule