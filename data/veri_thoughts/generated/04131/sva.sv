module Adder8_sva (
    input  logic       clk,
    input  logic [7:0] A,
    input  logic [7:0] B,
    input  logic       Cin,
    input  logic [7:0] Sum,
    input  logic       Cout
);

    // Combinational adder sampled on clk; the RTL has no reset.

    // The concatenated outputs equal the 9-bit addition of A, B, and Cin.
    check_full_add_result: assert property (
        @(posedge clk) {Cout, Sum} == ({1'b0, A} + {1'b0, B} + Cin)
    );

    // Sum is the low 8 bits of the addition result.
    check_sum_low_byte: assert property (
        @(posedge clk) Sum == ({1'b0, A} + {1'b0, B} + Cin)[7:0]
    );

    // Cout is the carry-out bit of the addition result.
    check_cout_carry_bit: assert property (
        @(posedge clk) Cout == ({1'b0, A} + {1'b0, B} + Cin)[8]
    );

    // Adding zero on B with no carry-in passes A through unchanged.
    check_zero_b_passthrough_a: assert property (
        @(posedge clk) (B == 8'h00 && Cin == 1'b0) |-> ({Cout, Sum} == {1'b0, A})
    );

    // Adding zero on A with no carry-in passes B through unchanged.
    check_zero_a_passthrough_b: assert property (
        @(posedge clk) (A == 8'h00 && Cin == 1'b0) |-> ({Cout, Sum} == {1'b0, B})
    );

    // Zero plus zero with zero carry-in produces a zero result.
    check_all_zero_result: assert property (
        @(posedge clk) (A == 8'h00 && B == 8'h00 && Cin == 1'b0) |-> (Sum == 8'h00 && Cout == 1'b0)
    );

endmodule