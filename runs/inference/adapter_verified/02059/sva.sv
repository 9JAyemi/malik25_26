module top_module_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic sel,
    input logic [3:0] OUT
);

// When sel is low, OUT selects B.
    check_sel_low_selects_b: assert property (
        @(posedge clk) !sel |-> (OUT == B)
    );

// When sel is high, OUT selects the twos complement of A.
    check_sel_high_selects_twos_comp: assert property (
        @(posedge clk) sel |-> (OUT == ~A + 4'd1)
    );

// The upper two bits of OUT are always zero (4-bit output).
    check_out_upper_bits_zero: assert property (
        @(posedge clk) OUT[3:2] == 2'b00
    );

// With sel low, OUT equals B.
    check_out_equals_b_when_sel_low: assert property (
        @(posedge clk) !sel |-> (OUT == B)
    );

// With sel high, OUT equals ~A + 4'd1.
    check_out_equals_twos_comp_when_sel_high: assert property (
        @(posedge clk) sel |-> (OUT == ~A + 4'd1)
    );

// With sel high, OUT equals A when A is zero.
    check_out_equals_a_when_sel_high_and_a_zero: assert property (
        @(posedge clk) sel && (A == 4'd0) |-> (OUT == A)
    );

// With sel high, OUT equals 4'hF when A is 4'hF.
    check_out_equals_all_ones_when_sel_high_and_a_ones: assert property (
        @(posedge clk) sel && (A == 4'hF) |-> (OUT == 4'hF)
    );

// With sel high, OUT equals 4'h8 when A is 4'h1.
    check_out_equals_minus8_when_sel_high_and_a_one: assert property (
        @(posedge clk) sel && (A == 4'h1) |-> (OUT == 4'h8)
    );

// With sel high, OUT equals 4'h0 when A is 4'h8.
    check_out_equals_zero_when_sel_high_and_a_eight: assert property (
        @(posedge clk) sel && (A == 4'h8) |-> (OUT == 4'h0)
    );

endmodule
