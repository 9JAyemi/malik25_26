module NOR3X1_sva (
    input logic CLK,
    input logic A,
    input logic B,
    input logic C,
    input logic Y
);
    // Y equals (A | B) & ~C.
    check_functional_equivalence: assert property (
        @(posedge CLK) disable iff (1'b0) Y == ((A | B) & ~C)
    );

    // If C is 1, Y must be 0.
    check_y_zero_when_C_is_one: assert property (
        @(posedge CLK) disable iff (1'b0) (C == 1'b1) |-> (Y == 1'b0)
    );

    // If A and B are both 0, Y must be 0.
    check_y_zero_when_A_and_B_zero: assert property (
        @(posedge CLK) disable iff (1'b0) ((A == 1'b0) && (B == 1'b0)) |-> (Y == 1'b0)
    );

    // If C is 0 and either A or B is 1, Y must be 1.
    check_y_one_when_C_zero_and_AorB_one: assert property (
        @(posedge CLK) disable iff (1'b0) ((C == 1'b0) && (A || B)) |-> (Y == 1'b1)
    );

    // If Y is 1, then C is 0 and at least one of A or B is 1.
    check_y_one_implies_C_zero_and_AorB_one: assert property (
        @(posedge CLK) disable iff (1'b0) (Y == 1'b1) |-> ((C == 1'b0) && (A || B))
    );

    // With known inputs, output must be known (no X/Z).
    check_no_x_when_inputs_known: assert property (
        @(posedge CLK) disable iff (1'b0) (!$isunknown({A,B,C})) |-> (!$isunknown(Y))
    );

    // If inputs are stable across a cycle, Y must be stable.
    check_stable_output_if_inputs_stable: assert property (
        @(posedge CLK) disable iff (1'b0) $stable({A,B,C}) |-> $stable(Y)
    );

    // On A rising with C=0, Y must be 1.
    check_y_one_on_rise_A_when_C_zero: assert property (
        @(posedge CLK) disable iff (1'b0) ($rose(A) && (C == 1'b0)) |-> (Y == 1'b1)
    );

    // On B rising with C=0, Y must be 1.
    check_y_one_on_rise_B_when_C_zero: assert property (
        @(posedge CLK) disable iff (1'b0) ($rose(B) && (C == 1'b0)) |-> (Y == 1'b1)
    );

    // On C rising, Y must be 0.
    check_y_zero_on_rise_C: assert property (
        @(posedge CLK) disable iff (1'b0) $rose(C) |-> (Y == 1'b0)
    );
endmodule