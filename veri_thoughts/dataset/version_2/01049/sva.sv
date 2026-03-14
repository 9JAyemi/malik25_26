module barrel_shifter_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [2:0] B,
    input logic [3:0] S,
    input logic C
);
    ///// Basic output relations /////
    // C always mirrors S[0].
    check_c_mirrors_s0: assert property (
        @(posedge clk) C == S[0]
    );
    // S equals one of the four priority-selected shift results.
    check_s_in_valid_set: assert property (
        @(posedge clk)
            (S == A) ||
            (S == {A[2:0], 1'b0}) ||
            (S == {A[1:0], 2'b0}) ||
            (S == {A[0], 3'b0})
    );

    ///// Priority selection by B /////
    // When B[2] is 1, S equals A and C equals A[0].
    check_b2_selects_a: assert property (
        @(posedge clk) B[2] |-> (S == A) && (C == A[0])
    );
    // When B[1] is 1 and B[2] is 0, S is A<<1 and C is 0.
    check_b1_selects_shift1: assert property (
        @(posedge clk) (!B[2] && B[1]) |-> (S == {A[2:0], 1'b0}) && (C == 1'b0)
    );
    // When only B[0] is 1 (and B[2:1]==0), S is A<<2 and C is 0.
    check_b0_selects_shift2: assert property (
        @(posedge clk) (!B[2] && !B[1] && B[0]) |-> (S == {A[1:0], 2'b0}) && (C == 1'b0)
    );
    // When B is 3'b000, S is A<<3 and C is 0.
    check_b000_selects_shift3: assert property (
        @(posedge clk) (!B[2] && !B[1] && !B[0]) |-> (S == {A[0], 3'b0}) && (C == 1'b0)
    );

    ///// Bit-level consequences /////
    // When B[2] is 0, LSB of S is 0.
    check_s0_zero_when_b2_zero: assert property (
        @(posedge clk) (!B[2]) |-> (S[0] == 1'b0)
    );
    // When selecting A<<1, S[3] equals A[2].
    check_msbit_mapping_b1: assert property (
        @(posedge clk) (!B[2] && B[1]) |-> (S[3] == A[2])
    );
    // When selecting A<<2, S[3] equals A[1].
    check_msbit_mapping_b0: assert property (
        @(posedge clk) (!B[2] && !B[1] && B[0]) |-> (S[3] == A[1])
    );
    // When selecting A<<3, S[3] equals A[0].
    check_msbit_mapping_b000: assert property (
        @(posedge clk) (!B[2] && !B[1] && !B[0]) |-> (S[3] == A[0])
    );
endmodule