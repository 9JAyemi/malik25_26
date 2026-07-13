module bitwise_and_sva (
    input logic clk,
    input logic [1:0] A,
    input logic [1:0] B,
    input logic [1:0] Y
);
    // Output equals bitwise AND of inputs (vector).
    check_and_vector: assert property (
        @(posedge clk) (Y == (A & B))
    );

    // Bit 0 output equals AND of inputs bit 0.
    check_and_bit0: assert property (
        @(posedge clk) (Y[0] == (A[0] & B[0]))
    );

    // Bit 1 output equals AND of inputs bit 1.
    check_and_bit1: assert property (
        @(posedge clk) (Y[1] == (A[1] & B[1]))
    );

    // Y[0] is 1 only when both A[0] and B[0] are 1 (same cycle).
    check_y0_only_when_both_high: assert property (
        @(posedge clk) Y[0] |=> (A[0] && B[0])
    );

    // Y[1] is 1 only when both A[1] and B[1] are 1 (same cycle).
    check_y1_only_when_both_high: assert property (
        @(posedge clk) Y[1] |=> (A[1] && B[1])
    );

    // If both A[0] and B[0] are 1, then Y[0] is 1 (same cycle).
    check_both_high_implies_y0: assert property (
        @(posedge clk) (A[0] && B[0]) |=> Y[0]
    );

    // If both A[1] and B[1] are 1, then Y[1] is 1 (same cycle).
    check_both_high_implies_y1: assert property (
        @(posedge clk) (A[1] && B[1]) |=> Y[1]
    );
endmodule