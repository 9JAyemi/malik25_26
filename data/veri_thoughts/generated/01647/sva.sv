module bitwise_and_sva (
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [7:0] C
);
    // Analysis: no clock/reset; pure combinational; C = A & B.

    // C equals A & B at all times.
    and_equivalence: assert property (
        @(posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or
          posedge A[4] or negedge A[4] or posedge A[5] or negedge A[5] or posedge A[6] or negedge A[6] or posedge A[7] or negedge A[7] or
          posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3] or
          posedge B[4] or negedge B[4] or posedge B[5] or negedge B[5] or posedge B[6] or negedge B[6] or posedge B[7] or negedge B[7])
        (C == (A & B))
    );

    // If A is zero, C must be zero.
    zero_output_when_A_zero: assert property (
        @(posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or
          posedge A[4] or negedge A[4] or posedge A[5] or negedge A[5] or posedge A[6] or negedge A[6] or posedge A[7] or negedge A[7] or
          posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3] or
          posedge B[4] or negedge B[4] or posedge B[5] or negedge B[5] or posedge B[6] or negedge B[6] or posedge B[7] or negedge B[7])
        (A == 8'h00) |-> (C == 8'h00)
    );

    // If B is zero, C must be zero.
    zero_output_when_B_zero: assert property (
        @(posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or
          posedge A[4] or negedge A[4] or posedge A[5] or negedge A[5] or posedge A[6] or negedge A[6] or posedge A[7] or negedge A[7] or
          posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3] or
          posedge B[4] or negedge B[4] or posedge B[5] or negedge B[5] or posedge B[6] or negedge B[6] or posedge B[7] or negedge B[7])
        (B == 8'h00) |-> (C == 8'h00)
    );

    // If B is all ones, C equals A.
    pass_through_A_when_B_all_ones: assert property (
        @(posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or
          posedge A[4] or negedge A[4] or posedge A[5] or negedge A[5] or posedge A[6] or negedge A[6] or posedge A[7] or negedge A[7] or
          posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3] or
          posedge B[4] or negedge B[4] or posedge B[5] or negedge B[5] or posedge B[6] or negedge B[6] or posedge B[7] or negedge B[7])
        (B == 8'hFF) |-> (C == A)
    );

    // If A is all ones, C equals B.
    pass_through_B_when_A_all_ones: assert property (
        @(posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or
          posedge A[4] or negedge A[4] or posedge A[5] or negedge A[5] or posedge A[6] or negedge A[6] or posedge A[7] or negedge A[7] or
          posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3] or
          posedge B[4] or negedge B[4] or posedge B[5] or negedge B[5] or posedge B[6] or negedge B[6] or posedge B[7] or negedge B[7])
        (A == 8'hFF) |-> (C == B)
    );

    // C has no 1s where A has 0s.
    no_one_bits_outside_A: assert property (
        @(posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or
          posedge A[4] or negedge A[4] or posedge A[5] or negedge A[5] or posedge A[6] or negedge A[6] or posedge A[7] or negedge A[7] or
          posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3] or
          posedge B[4] or negedge B[4] or posedge B[5] or negedge B[5] or posedge B[6] or negedge B[6] or posedge B[7] or negedge B[7])
        ((C & ~A) == 8'h00)
    );

    // C has no 1s where B has 0s.
    no_one_bits_outside_B: assert property (
        @(posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or
          posedge A[4] or negedge A[4] or posedge A[5] or negedge A[5] or posedge A[6] or negedge A[6] or posedge A[7] or negedge A[7] or
          posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3] or
          posedge B[4] or negedge B[4] or posedge B[5] or negedge B[5] or posedge B[6] or negedge B[6] or posedge B[7] or negedge B[7])
        ((C & ~B) == 8'h00)
    );
endmodule