module bitwise_and_sva (
    input logic clk,
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [7:0] C
);

// C must equal the bitwise AND of A and B.
    check_output_matches_and: assert property (
        @(posedge clk) C == (A & B)
    );

// A high bit forces the corresponding C bit high.
    check_a_high_sets_c_high: assert property (
        @(posedge clk) (A[7] == 1'b1) |-> (C[7] == 1'b1)
    );

// A low bit forces the corresponding C bit low.
    check_a_low_sets_c_low: assert property (
        @(posedge clk) (A[7] == 1'b0) |-> (C[7] == 1'b0)
    );

// B high bit forces the corresponding C bit high.
    check_b_high_sets_c_high: assert property (
        @(posedge clk) (B[7] == 1'b1) |-> (C[7] == 1'b1)
    );

// B low bit forces the corresponding C bit low.
    check_b_low_sets_c_low: assert property (
        @(posedge clk) (B[7] == 1'b0) |-> (C[7] == 1'b0)
    );

// A high C bit requires both A and B high at that bit.
    check_c_high_requires_a_and_b_high: assert property (
        @(posedge clk) (C[7] == 1'b1) |-> ((A[7] == 1'b1) && (B[7] == 1'b1))
    );

endmodule
