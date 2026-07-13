module nor3_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic Y
);
    // Y equals A & B & ~C at all times.
    check_function_equivalence: assert property (
        @(posedge A or posedge B or posedge C or posedge Y) Y == (A & B & ~C)
    );

    // If C is HIGH then Y must be LOW.
    check_c_high_forces_y_low: assert property (
        @(posedge A or posedge B or posedge C or posedge Y) (C == 1'b1) |-> (Y == 1'b0)
    );

    // If A is LOW then Y must be LOW.
    check_a_low_forces_y_low: assert property (
        @(posedge A or posedge B or posedge C or posedge Y) (A == 1'b0) |-> (Y == 1'b0)
    );

    // If B is LOW then Y must be LOW.
    check_b_low_forces_y_low: assert property (
        @(posedge A or posedge B or posedge C or posedge Y) (B == 1'b0) |-> (Y == 1'b0)
    );

    // If A and B are HIGH and C is LOW then Y must be HIGH.
    check_ab1_c0_implies_y1: assert property (
        @(posedge A or posedge B or posedge C or posedge Y) (A && B && !C) |-> (Y == 1'b1)
    );

    // If Y is HIGH then A and B are HIGH and C is LOW.
    check_y1_implies_ab1_c0: assert property (
        @(posedge A or posedge B or posedge C or posedge Y) (Y == 1'b1) |-> (A && B && !C)
    );

    // A rising Y can only occur when A and B are HIGH and C is LOW.
    check_y_rise_condition: assert property (
        @(posedge A or posedge B or posedge C or posedge Y) $rose(Y) |-> (A && B && !C)
    );

    // Y can only change when at least one input changes.
    check_y_change_requires_input_change: assert property (
        @(posedge A or posedge B or posedge C or posedge Y) ($rose(Y) || $fell(Y)) |-> ($rose(A) || $fell(A) || $rose(B) || $fell(B) || $rose(C) || $fell(C))
    );

    // If all inputs are stable, Y must remain stable.
    check_inputs_stable_keeps_y_stable: assert property (
        @(posedge A or posedge B or posedge C or posedge Y) ($stable(A) && $stable(B) && $stable(C)) |-> $stable(Y)
    );
endmodule