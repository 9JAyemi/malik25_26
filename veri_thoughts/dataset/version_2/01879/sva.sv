module bitwise_and_sva (
    input logic CLK,
    input logic [15:0] A,
    input logic [15:0] B,
    input logic [15:0] C
);
    // C equals bitwise AND of A and B.
    check_and_functional: assert property (
        @(posedge CLK) disable iff (1'b0) (C == (A & B))
    );

    // No C bit can be 1 unless both A and B bits are 1.
    check_no_spurious_ones: assert property (
        @(posedge CLK) disable iff (1'b0) ((C & (~A | ~B)) == 16'h0000)
    );

    // All (A & B) 1-bits must appear in C (no missing ones).
    check_no_missing_ones: assert property (
        @(posedge CLK) disable iff (1'b0) (((A & B) & ~C) == 16'h0000)
    );

    // If A is all zeros, C is all zeros.
    check_zero_when_A_zero: assert property (
        @(posedge CLK) disable iff (1'b0) (A == 16'h0000) |-> (C == 16'h0000)
    );

    // If B is all zeros, C is all zeros.
    check_zero_when_B_zero: assert property (
        @(posedge CLK) disable iff (1'b0) (B == 16'h0000) |-> (C == 16'h0000)
    );

    // If A is all ones, C passes B unchanged.
    check_pass_through_when_A_all_ones: assert property (
        @(posedge CLK) disable iff (1'b0) (A == 16'hFFFF) |-> (C == B)
    );

    // If B is all ones, C passes A unchanged.
    check_pass_through_when_B_all_ones: assert property (
        @(posedge CLK) disable iff (1'b0) (B == 16'hFFFF) |-> (C == A)
    );
endmodule