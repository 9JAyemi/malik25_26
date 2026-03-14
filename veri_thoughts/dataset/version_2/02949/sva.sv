module twos_complement_sva (
    input logic clk,
    input logic [3:0] in,
    input logic [3:0] out
);
    // No clock or reset in RTL; purely combinational; function: out = ~in + 1'b1 (4-bit two's complement).

    // out equals bitwise-not(in) plus 1 each cycle.
    check_twos_function: assert property (
        @(posedge clk) out == (~in + 1'b1)
    );

    // Two's complement is an involution: ~out + 1 equals in.
    check_involution: assert property (
        @(posedge clk) (~out + 1'b1) == in
    );

    // Sum of in and out is zero modulo 16.
    check_sum_zero_mod16: assert property (
        @(posedge clk) (in + out) == 4'h0
    );

    // Zero maps to zero.
    check_zero_maps_to_zero: assert property (
        @(posedge clk) (in == 4'h0) |-> (out == 4'h0)
    );

    // Zero output implies zero input (bijectivity at zero).
    check_zero_out_implies_zero_in: assert property (
        @(posedge clk) (out == 4'h0) |-> (in == 4'h0)
    );

    // 8 is a fixed point in 4-bit two's complement.
    check_eight_fixed_point: assert property (
        @(posedge clk) (in == 4'h8) |-> (out == 4'h8)
    );

    // LSB is preserved by two's complement.
    check_lsb_preserved: assert property (
        @(posedge clk) out[0] == in[0]
    );

    // If in equals out, it must be 0 or 8.
    check_fixed_points_only_0_or_8: assert property (
        @(posedge clk) (in == out) |-> ((in == 4'h0) || (in == 4'h8))
    );

    // Corner case: -1 (0xF) maps to +1 (0x1).
    check_F_to_1: assert property (
        @(posedge clk) (in == 4'hF) |-> (out == 4'h1)
    );

    // Corner case: +1 (0x1) maps to -1 (0xF).
    check_1_to_F: assert property (
        @(posedge clk) (in == 4'h1) |-> (out == 4'hF)
    );
endmodule