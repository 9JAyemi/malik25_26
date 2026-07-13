module addsub4_sva (
    // No clock/reset in RTL; pure combinational. Sampling clock provided here.
    input logic CLK,
    // DUT ports
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       M,
    input logic [3:0] Y,
    // Internal nets from RTL (fa1 chain)
    input logic [3:0] C,
    input logic [3:0] S
);

    ///// Y functional behavior /////
    // When M==0, Y is A+B (truncated to 4 bits).
    y_add: assert property (
        @(posedge CLK) (M == 1'b0) |-> (Y == ((A + B) & 4'hF))
    );
    // When M==1, Y is A-B (truncated to 4 bits).
    y_sub: assert property (
        @(posedge CLK) (M == 1'b1) |-> (Y == ((A - B) & 4'hF))
    );

    ///// fa1_0 (bit 0) behavior /////
    // S[0] equals A[0] ^ B[0] ^ M.
    fa0_sum_def: assert property (
        @(posedge CLK) S[0] == (A[0] ^ B[0] ^ M)
    );
    // C[0] equals (A[0]&B[0]) | (M & (A[0]^B[0])).
    fa0_carry_def: assert property (
        @(posedge CLK) C[0] == ((A[0] & B[0]) | (M & (A[0] ^ B[0])))
    );

    ///// fa1_1 (bit 1) behavior /////
    // S[1] equals A[1] ^ B[1] ^ C[0].
    fa1_sum_def: assert property (
        @(posedge CLK) S[1] == (A[1] ^ B[1] ^ C[0])
    );
    // C[1] equals (A[1]&B[1]) | (C[0] & (A[1]^B[1])).
    fa1_carry_def: assert property (
        @(posedge CLK) C[1] == ((A[1] & B[1]) | (C[0] & (A[1] ^ B[1])))
    );

    ///// fa1_2 (bit 2) behavior /////
    // S[2] equals A[2] ^ B[2] ^ C[1].
    fa2_sum_def: assert property (
        @(posedge CLK) S[2] == (A[2] ^ B[2] ^ C[1])
    );
    // C[2] equals (A[2]&B[2]) | (C[1] & (A[2]^B[2])).
    fa2_carry_def: assert property (
        @(posedge CLK) C[2] == ((A[2] & B[2]) | (C[1] & (A[2] ^ B[2])))
    );

    ///// fa1_3 (bit 3) behavior /////
    // S[3] equals A[3] ^ B[3] ^ C[2].
    fa3_sum_def: assert property (
        @(posedge CLK) S[3] == (A[3] ^ B[3] ^ C[2])
    );
    // C[3] equals (A[3]&B[3]) | (C[2] & (A[3]^B[3])).
    fa3_carry_def: assert property (
        @(posedge CLK) C[3] == ((A[3] & B[3]) | (C[2] & (A[3] ^ B[3])))
    );

endmodule