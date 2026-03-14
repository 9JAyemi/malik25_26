module mux16_sva (
    input logic [15:0] MO,
    input logic [15:0] A,
    input logic [15:0] B,
    input logic S
);
    // MO equals selected input
    check_output_matches_mux: assert property (
        @(posedge S or negedge S
          or posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1]
          or posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3]
          or posedge A[4] or negedge A[4] or posedge A[5] or negedge A[5]
          or posedge A[6] or negedge A[6] or posedge A[7] or negedge A[7]
          or posedge A[8] or negedge A[8] or posedge A[9] or negedge A[9]
          or posedge A[10] or negedge A[10] or posedge A[11] or negedge A[11]
          or posedge A[12] or negedge A[12] or posedge A[13] or negedge A[13]
          or posedge A[14] or negedge A[14] or posedge A[15] or negedge A[15]
          or posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1]
          or posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3]
          or posedge B[4] or negedge B[4] or posedge B[5] or negedge B[5]
          or posedge B[6] or negedge B[6] or posedge B[7] or negedge B[7]
          or posedge B[8] or negedge B[8] or posedge B[9] or negedge B[9]
          or posedge B[10] or negedge B[10] or posedge B[11] or negedge B[11]
          or posedge B[12] or negedge B[12] or posedge B[13] or negedge B[13]
          or posedge B[14] or negedge B[14] or posedge B[15] or negedge B[15]
        ) MO == (S ? B : A)
    );

    // When S=0, MO equals A
    check_select0_routes_A: assert property (
        @(posedge S or negedge S
          or posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1]
          or posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3]
          or posedge A[4] or negedge A[4] or posedge A[5] or negedge A[5]
          or posedge A[6] or negedge A[6] or posedge A[7] or negedge A[7]
          or posedge A[8] or negedge A[8] or posedge A[9] or negedge A[9]
          or posedge A[10] or negedge A[10] or posedge A[11] or negedge A[11]
          or posedge A[12] or negedge A[12] or posedge A[13] or negedge A[13]
          or posedge A[14] or negedge A[14] or posedge A[15] or negedge A[15]
          or posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1]
          or posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3]
          or posedge B[4] or negedge B[4] or posedge B[5] or negedge B[5]
          or posedge B[6] or negedge B[6] or posedge B[7] or negedge B[7]
          or posedge B[8] or negedge B[8] or posedge B[9] or negedge B[9]
          or posedge B[10] or negedge B[10] or posedge B[11] or negedge B[11]
          or posedge B[12] or negedge B[12] or posedge B[13] or negedge B[13]
          or posedge B[14] or negedge B[14] or posedge B[15] or negedge B[15]
        ) (S == 1'b0) |-> (MO == A)
    );

    // When S=1, MO equals B
    check_select1_routes_B: assert property (
        @(posedge S or negedge S
          or posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1]
          or posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3]
          or posedge A[4] or negedge A[4] or posedge A[5] or negedge A[5]
          or posedge A[6] or negedge A[6] or posedge A[7] or negedge A[7]
          or posedge A[8] or negedge A[8] or posedge A[9] or negedge A[9]
          or posedge A[10] or negedge A[10] or posedge A[11] or negedge A[11]
          or posedge A[12] or negedge A[12] or posedge A[13] or negedge A[13]
          or posedge A[14] or negedge A[14] or posedge A[15] or negedge A[15]
          or posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1]
          or posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3]
          or posedge B[4] or negedge B[4] or posedge B[5] or negedge B[5]
          or posedge B[6] or negedge B[6] or posedge B[7] or negedge B[7]
          or posedge B[8] or negedge B[8] or posedge B[9] or negedge B[9]
          or posedge B[10] or negedge B[10] or posedge B[11] or negedge B[11]
          or posedge B[12] or negedge B[12] or posedge B[13] or negedge B[13]
          or posedge B[14] or negedge B[14] or posedge B[15] or negedge B[15]
        ) (S == 1'b1) |-> (MO == B)
    );

    // If inputs are equal, MO equals that value
    check_equal_inputs_passthrough: assert property (
        @(posedge S or negedge S
          or posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1]
          or posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3]
          or posedge A[4] or negedge A[4] or posedge A[5] or negedge A[5]
          or posedge A[6] or negedge A[6] or posedge A[7] or negedge A[7]
          or posedge A[8] or negedge A[8] or posedge A[9] or negedge A[9]
          or posedge A[10] or negedge A[10] or posedge A[11] or negedge A[11]
          or posedge A[12] or negedge A[12] or posedge A[13] or negedge A[13]
          or posedge A[14] or negedge A[14] or posedge A[15] or negedge A[15]
          or posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1]
          or posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3]
          or posedge B[4] or negedge B[4] or posedge B[5] or negedge B[5]
          or posedge B[6] or negedge B[6] or posedge B[7] or negedge B[7]
          or posedge B[8] or negedge B[8] or posedge B[9] or negedge B[9]
          or posedge B[10] or negedge B[10] or posedge B[11] or negedge B[11]
          or posedge B[12] or negedge B[12] or posedge B[13] or negedge B[13]
          or posedge B[14] or negedge B[14] or posedge B[15] or negedge B[15]
        ) (A == B) |-> (MO == A)
    );

    // If A!=B and MO equals B, S must be 1
    check_infer_sel1_when_out_eq_B_and_inputs_diff: assert property (
        @(posedge S or negedge S
          or posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1]
          or posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3]
          or posedge A[4] or negedge A[4] or posedge A[5] or negedge A[5]
          or posedge A[6] or negedge A[6] or posedge A[7] or negedge A[7]
          or posedge A[8] or negedge A[8] or posedge A[9] or negedge A[9]
          or posedge A[10] or negedge A[10] or posedge A[11] or negedge A[11]
          or posedge A[12] or negedge A[12] or posedge A[13] or negedge A[13]
          or posedge A[14] or negedge A[14] or posedge A[15] or negedge A[15]
          or posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1]
          or posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3]
          or posedge B[4] or negedge B[4] or posedge B[5] or negedge B[5]
          or posedge B[6] or negedge B[6] or posedge B[7] or negedge B[7]
          or posedge B[8] or negedge B[8] or posedge B[9] or negedge B[9]
          or posedge B[10] or negedge B[10] or posedge B[11] or negedge B[11]
          or posedge B[12] or negedge B[12] or posedge B[13] or negedge B[13]
          or posedge B[14] or negedge B[14] or posedge B[15] or negedge B[15]
        ) (A != B && MO == B) |-> (S == 1'b1)
    );

    // If A!=B and MO equals A, S must be 0
    check_infer_sel0_when_out_eq_A_and_inputs_diff: assert property (
        @(posedge S or negedge S
          or posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1]
          or posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3]
          or posedge A[4] or negedge A[4] or posedge A[5] or negedge A[5]
          or posedge A[6] or negedge A[6] or posedge A[7] or negedge A[7]
          or posedge A[8] or negedge A[8] or posedge A[9] or negedge A[9]
          or posedge A[10] or negedge A[10] or posedge A[11] or negedge A[11]
          or posedge A[12] or negedge A[12] or posedge A[13] or negedge A[13]
          or posedge A[14] or negedge A[14] or posedge A[15] or negedge A[15]
          or posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1]
          or posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3]
          or posedge B[4] or negedge B[4] or posedge B[5] or negedge B[5]
          or posedge B[6] or negedge B[6] or posedge B[7] or negedge B[7]
          or posedge B[8] or negedge B[8] or posedge B[9] or negedge B[9]
          or posedge B[10] or negedge B[10] or posedge B[11] or negedge B[11]
          or posedge B[12] or negedge B[12] or posedge B[13] or negedge B[13]
          or posedge B[14] or negedge B[14] or posedge B[15] or negedge B[15]
        ) (A != B && MO == A) |-> (S == 1'b0)
    );

    // On rising S, output selects B
    check_rose_S_selects_B: assert property (
        @(posedge S or negedge S
          or posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1]
          or posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3]
          or posedge A[4] or negedge A[4] or posedge A[5] or negedge A[5]
          or posedge A[6] or negedge A[6] or posedge A[7] or negedge A[7]
          or posedge A[8] or negedge A[8] or posedge A[9] or negedge A[9]
          or posedge A[10] or negedge A[10] or posedge A[11] or negedge A[11]
          or posedge A[12] or negedge A[12] or posedge A[13] or negedge A[13]
          or posedge A[14] or negedge A[14] or posedge A[15] or negedge A[15]
          or posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1]
          or posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3]
          or posedge B[4] or negedge B[4] or posedge B[5] or negedge B[5]
          or posedge B[6] or negedge B[6] or posedge B[7] or negedge B[7]
          or posedge B[8] or negedge B[8] or posedge B[9] or negedge B[9]
          or posedge B[10] or negedge B[10] or posedge B[11] or negedge B[11]
          or posedge B[12] or negedge B[12] or posedge B[13] or negedge B[13]
          or posedge B[14] or negedge B[14] or posedge B[15] or negedge B[15]
        ) $rose(S) |-> (MO == B)
    );

    // On falling S, output selects A
    check_fell_S_selects_A: assert property (
        @(posedge S or negedge S
          or posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1]
          or posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3]
          or posedge A[4] or negedge A[4] or posedge A[5] or negedge A[5]
          or posedge A[6] or negedge A[6] or posedge A[7] or negedge A[7]
          or posedge A[8] or negedge A[8] or posedge A[9] or negedge A[9]
          or posedge A[10] or negedge A[10] or posedge A[11] or negedge A[11]
          or posedge A[12] or negedge A[12] or posedge A[13] or negedge A[13]
          or posedge A[14] or negedge A[14] or posedge A[15] or negedge A[15]
          or posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1]
          or posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3]
          or posedge B[4] or negedge B[4] or posedge B[5] or negedge B[5]
          or posedge B[6] or negedge B[6] or posedge B[7] or negedge B[7]
          or posedge B[8] or negedge B[8] or posedge B[9] or negedge B[9]
          or posedge B[10] or negedge B[10] or posedge B[11] or negedge B[11]
          or posedge B[12] or negedge B[12] or posedge B[13] or negedge B[13]
          or posedge B[14] or negedge B[14] or posedge B[15] or negedge B[15]
        ) $fell(S) |-> (MO == A)
    );

endmodule