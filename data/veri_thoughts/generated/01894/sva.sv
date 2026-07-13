module ascending_order_sva (
    input logic CLK,
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [7:0] C,
    input logic Y
);
    ///// Functional equivalence /////
    // Y reflects strict ascending order A < B < C.
    check_y_definition: assert property (
        @(posedge CLK) Y == ((A < B) && (B < C))
    );

    ///// Consequences of the definition /////
    // If A >= B, Y must be 0.
    check_y_zero_when_A_ge_B: assert property (
        @(posedge CLK) (A >= B) |-> (Y == 1'b0)
    );
    // If B >= C, Y must be 0.
    check_y_zero_when_B_ge_C: assert property (
        @(posedge CLK) (B >= C) |-> (Y == 1'b0)
    );
    // If Y is 1, then A < C (implied by A < B and B < C).
    check_transitive_A_lt_C_when_Y_one: assert property (
        @(posedge CLK) (Y == 1'b1) |-> (A < C)
    );

    ///// Combinational determinism /////
    // If A,B,C are unchanged from the previous cycle, Y must be unchanged.
    check_output_stable_when_inputs_stable: assert property (
        @(posedge CLK) (A == $past(A) && B == $past(B) && C == $past(C)) |-> (Y == $past(Y))
    );
    // If Y changes, at least one of A,B,C must have changed.
    check_output_change_requires_input_change: assert property (
        @(posedge CLK) (Y != $past(Y)) |-> ((A != $past(A)) || (B != $past(B)) || (C != $past(C)))
    );
endmodule