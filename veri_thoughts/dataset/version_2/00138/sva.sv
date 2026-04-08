module four_bit_adder_assertions (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic [3:0] Sum,
    input logic Cout
);

    // Full result must equal A plus B plus carry-in.
    check_full_add_result: assert property (
        @(posedge clk) {Cout, Sum} == (A + B + Cin)
    );

    // Sum bit 0 must match the low-bit full-adder parity.
    check_lsb_sum_bit: assert property (
        @(posedge clk) Sum[0] == (A[0] ^ B[0] ^ Cin)
    );

    // Adding zero with no carry-in must pass A through.
    check_a_passthrough: assert property (
        @(posedge clk) ((B == 4'h0) && (Cin == 1'b0)) |-> ({Cout, Sum} == {1'b0, A})
    );

    // Adding zero with no carry-in must pass B through.
    check_b_passthrough: assert property (
        @(posedge clk) ((A == 4'h0) && (Cin == 1'b0)) |-> ({Cout, Sum} == {1'b0, B})
    );

    // Zero inputs with zero carry-in must produce zero output.
    check_zero_result: assert property (
        @(posedge clk) ((A == 4'h0) && (B == 4'h0) && (Cin == 1'b0)) |-> ({Cout, Sum} == 5'h0)
    );

    // All-ones inputs with carry-in must produce the maximum 5-bit sum.
    check_max_result: assert property (
        @(posedge clk) ((A == 4'hF) && (B == 4'hF) && (Cin == 1'b1)) |-> ({Cout, Sum} == 5'h1F)
    );

endmodule