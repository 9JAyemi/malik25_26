module mux_2_to_1_sva (
    input logic CLK,   // sampling clock for assertions
    input logic A,
    input logic B,
    input logic S,
    input logic Y
);
    // When S==0, Y must equal A.
    check_select_0_routes_A: assert property (
        @(posedge CLK) disable iff (1'b0) (S == 1'b0) |-> (Y == A)
    );

    // When S==1, Y must equal B.
    check_select_1_routes_B: assert property (
        @(posedge CLK) disable iff (1'b0) (S == 1'b1) |-> (Y == B)
    );

    // If A and B are equal, Y must equal them regardless of S.
    check_equal_inputs_forward: assert property (
        @(posedge CLK) disable iff (1'b0) (A == B) |-> (Y == A)
    );

    // If S==1 and Y equals A, then inputs must be equal.
    check_consistency_S1: assert property (
        @(posedge CLK) disable iff (1'b0) (S == 1'b1 && Y == A) |-> (A == B)
    );

    // If S==0 and Y equals B, then inputs must be equal.
    check_consistency_S0: assert property (
        @(posedge CLK) disable iff (1'b0) (S == 1'b0 && Y == B) |-> (A == B)
    );

    // If A!=B and Y equals A, then S must be 0.
    check_inverse_on_A: assert property (
        @(posedge CLK) disable iff (1'b0) ((A != B) && (Y == A)) |-> (S == 1'b0)
    );

    // If A!=B and Y equals B, then S must be 1.
    check_inverse_on_B: assert property (
        @(posedge CLK) disable iff (1'b0) ((A != B) && (Y == B)) |-> (S == 1'b1)
    );
endmodule