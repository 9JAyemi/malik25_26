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

// A high bit must appear in C when both A and B have that bit high.
    check_high_bit_propagates: assert property (
        @(posedge clk) (A[i] && B[i]) |-> (C[i] == 1'b1)
    );

// A low bit must force C low in that bit position.
    check_low_bit_blocks: assert property (
        @(posedge clk) (!A[i] || !B[i]) |-> (C[i] == 1'b0)
    );

// C can only have bits set where both A and B have those bits set.
    check_no_spurious_ones: assert property (
        @(posedge clk) (C[i] == 1'b1) |-> (A[i] && B[i])
    );

endmodule
