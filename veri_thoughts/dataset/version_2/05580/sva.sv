module binary_adder_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic [3:0] C
);

    // clk is the sampling clock for this combinational block.

    // Output matches the 4-bit sum of A, B, and Cin.
    check_total_sum: assert property (
        @(posedge clk) C == (A + B + Cin)
    );

    // With Cin low, output is the 4-bit sum of A and B.
    check_sum_without_carry_in: assert property (
        @(posedge clk) (Cin == 1'b0) |-> (C == (A + B))
    );

    // With Cin high, output is the 4-bit sum of A, B, and one.
    check_sum_with_carry_in: assert property (
        @(posedge clk) (Cin == 1'b1) |-> (C == (A + B + 1'b1))
    );

    // Zero inputs with no carry-in produce zero.
    check_zero_inputs_no_carry: assert property (
        @(posedge clk) (A == 4'h0 && B == 4'h0 && Cin == 1'b0) |-> (C == 4'h0)
    );

    // Zero inputs with carry-in produce one.
    check_zero_inputs_with_carry: assert property (
        @(posedge clk) (A == 4'h0 && B == 4'h0 && Cin == 1'b1) |-> (C == 4'h1)
    );

    // The least-significant sum bit matches xor addition.
    check_lsb_sum: assert property (
        @(posedge clk) C[0] == (A[0] ^ B[0] ^ Cin)
    );

    // Overflow is truncated to the low 4 bits.
    check_overflow_truncation: assert property (
        @(posedge clk) (A == 4'hF && B == 4'h1 && Cin == 1'b0) |-> (C == 4'h0)
    );

    // Full-scale addition with carry-in keeps only the low 4 bits.
    check_max_sum_truncation: assert property (
        @(posedge clk) (A == 4'hF && B == 4'hF && Cin == 1'b1) |-> (C == 4'hF)
    );

endmodule