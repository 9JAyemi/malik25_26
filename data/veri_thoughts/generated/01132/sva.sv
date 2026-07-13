module XOR2_NAND_sva (
    input logic CLK,
    input logic RESETn,
    input logic A,
    input logic B,
    input logic Y
);
    // Y implements A XOR B.
    check_y_is_xor_of_a_b: assert property (
        @(posedge CLK) disable iff (!RESETn) (Y == (A ^ B))
    );

    // When A==0, Y must equal B.
    check_y_equals_b_when_a_zero: assert property (
        @(posedge CLK) disable iff (!RESETn) (A == 1'b0) |-> (Y == B)
    );

    // When A==1, Y must equal ~B.
    check_y_equals_notb_when_a_one: assert property (
        @(posedge CLK) disable iff (!RESETn) (A == 1'b1) |-> (Y == ~B)
    );

    // When B==0, Y must equal A.
    check_y_equals_a_when_b_zero: assert property (
        @(posedge CLK) disable iff (!RESETn) (B == 1'b0) |-> (Y == A)
    );

    // When B==1, Y must equal ~A.
    check_y_equals_nota_when_b_one: assert property (
        @(posedge CLK) disable iff (!RESETn) (B == 1'b1) |-> (Y == ~A)
    );

    // If inputs are equal, Y must be 0.
    check_y_low_when_inputs_equal: assert property (
        @(posedge CLK) disable iff (!RESETn) (A == B) |-> (Y == 1'b0)
    );

    // If inputs differ, Y must be 1.
    check_y_high_when_inputs_different: assert property (
        @(posedge CLK) disable iff (!RESETn) (A != B) |-> (Y == 1'b1)
    );

    // Y's toggle between cycles equals parity of input toggles.
    check_y_toggle_parity_matches_inputs: assert property (
        @(posedge CLK) disable iff (!RESETn) ((Y ^ $past(Y)) == ((A ^ $past(A)) ^ (B ^ $past(B))))
    );

    // If only A changes and B is stable, Y must change.
    check_y_changes_when_only_a_changes: assert property (
        @(posedge CLK) disable iff (!RESETn) (A != $past(A) && B == $past(B)) |-> (Y != $past(Y))
    );

    // If only B changes and A is stable, Y must change.
    check_y_changes_when_only_b_changes: assert property (
        @(posedge CLK) disable iff (!RESETn) (B != $past(B) && A == $past(A)) |-> (Y != $past(Y))
    );
endmodule