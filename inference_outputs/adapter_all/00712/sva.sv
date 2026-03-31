module adder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] C
);
    // C equals A + B (4-bit wraparound).
    check_sum_matches_add: assert property (
        @(posedge A[0] or posedge A[1] or posedge A[2] or posedge A[3] or
          posedge B[0] or posedge B[1] or posedge B[2] or posedge B[3] or
          posedge C[0] or posedge C[1] or posedge C[2] or posedge C[3])
        C == (A + B)
    );

    // If A is zero, C equals B.
    check_zero_A_passthrough: assert property (
        @(posedge A[0] or posedge A[1] or posedge A[2] or posedge A[3] or
          posedge B[0] or posedge B[1] or posedge B[2] or posedge B[3] or
          posedge C[0] or posedge C[1] or posedge C[2] or posedge C[3])
        (A == 4'h0) |-> (C == B)
    );

    // If B is zero, C equals A.
    check_zero_B_passthrough: assert property (
        @(posedge A[0] or posedge A[1] or posedge A[2] or posedge A[3] or
          posedge B[0] or posedge B[1] or posedge B[2] or posedge B[3] or
          posedge C[0] or posedge C[1] or posedge C[2] or posedge C[3])
        (B == 4'h0) |-> (C == A)
    );

    // If A and B are stable, C is stable.
    check_stability_when_inputs_stable: assert property (
        @(posedge A[0] or posedge A[1] or posedge A[2] or posedge A[3] or
          posedge B[0] or posedge B[1] or posedge B[2] or posedge B[3] or
          posedge C[0] or posedge C[1] or posedge C[2] or posedge C[3])
        ($stable(A) && $stable(B)) |-> $stable(C)
    );

    // If A is stable and B changes, C changes.
    check_C_changes_when_B_changes: assert property (
        @(posedge A[0] or posedge A[1] or posedge A[2] or posedge A[3] or
          posedge B[0] or posedge B[1] or posedge B[2] or posedge B[3] or
          posedge C[0] or posedge C[1] or posedge C[2] or posedge C[3])
        ($stable(A) && $changed(B)) |-> $changed(C)
    );

    // If B is stable and A changes, C changes.
    check_C_changes_when_A_changes: assert property (
        @(posedge A[0] or posedge A[1] or posedge A[2] or posedge A[3] or
          posedge B[0] or posedge B[1] or posedge B[2] or posedge B[3] or
          posedge C[0] or posedge C[1] or posedge C[2] or posedge C[3])
        ($stable(B) && $changed(A)) |-> $changed(C)
    );

    // If A and B are equal, C equals A (commutativity).
    check_commutativity: assert property (
        @(posedge A[0] or posedge A[1] or posedge A[2] or posedge A[3] or
          posedge B[0] or posedge B[1] or posedge B[2] or posedge B[3] or
          posedge C[0] or posedge C[1] or posedge C[2] or posedge C[3])
        (A == B) |-> (C == A)
    );

    // If A is all ones and B is all ones, C is all ones (4-bit wrap).
    check_all_ones_plus_all_ones: assert property (
        @(posedge A[0] or posedge A[1] or posedge A[2] or posedge A[3] or
          posedge B[0] or posedge B[1] or posedge B[2] or posedge B[3] or
          posedge C[0] or posedge C[1] or posedge C[2] or posedge C[3])
        (A == 4'hF && B == 4'hF) |-> (C == 4'hF)
    );

    // If A is all zeros and B is all ones, C is all ones (4-bit wrap).
    check_zero_plus_all_ones: assert property (
        @(posedge A[0] or posedge A[1] or posedge A[2] or posedge A[3] or
          posedge B[0] or posedge B[1] or posedge B[2] or posedge B[3] or
          posedge C[0] or posedge C[1] or posedge C[2] or posedge C[3])
        (A == 4'h0 && B == 4'hF) |-> (C == 4'hF)
    );

    // If A is all ones and B is all zeros, C is all ones (4-bit wrap).
    check_all_ones_plus_zero: assert property (
        @(posedge A[0] or posedge A[1] or posedge A[2] or posedge A[3] or
          posedge B[0] or posedge B[1] or posedge B[2] or posedge B[3] or
          posedge C[0] or posedge C[1] or posedge C[2] or posedge C[3])
        (A == 4'hF && B == 4'h0) |-> (C == 4'hF)
    );
endmodule