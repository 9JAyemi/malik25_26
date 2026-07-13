module sky130_fd_sc_ms__o32a_sva (
    input logic CLK,
    input logic X,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic B2
);
    ///// Combinational function checks (clocked) /////
    // X must equal (A1|A2|A3) & (B1|B2).
    check_functional_equivalence: assert property (
        @(posedge CLK) X == ((A1 | A2 | A3) & (B1 | B2))
    );

    // If X is HIGH, both input groups' ORs must be HIGH.
    check_X_high_implies_groups_high: assert property (
        @(posedge CLK) X |-> ((A1 | A2 | A3) & (B1 | B2))
    );

    // If both input groups' ORs are HIGH, X must be HIGH.
    check_groups_high_implies_X_high: assert property (
        @(posedge CLK) ((A1 | A2 | A3) & (B1 | B2)) |-> (X == 1'b1)
    );

    // If A-group OR is LOW, X must be LOW.
    check_X_zero_when_Agroup_zero: assert property (
        @(posedge CLK) ~(A1 | A2 | A3) |-> (X == 1'b0)
    );

    // If B-group OR is LOW, X must be LOW.
    check_X_zero_when_Bgroup_zero: assert property (
        @(posedge CLK) ~(B1 | B2) |-> (X == 1'b0)
    );

    ///// Input transition effects /////
    // Rising A1 with B-group HIGH forces X HIGH.
    check_A1_rise_sets_X_when_Bgroup_one: assert property (
        @(posedge CLK) $rose(A1) && (B1 | B2) |-> (X == 1'b1)
    );

    // Rising A2 with B-group HIGH forces X HIGH.
    check_A2_rise_sets_X_when_Bgroup_one: assert property (
        @(posedge CLK) $rose(A2) && (B1 | B2) |-> (X == 1'b1)
    );

    // Rising A3 with B-group HIGH forces X HIGH.
    check_A3_rise_sets_X_when_Bgroup_one: assert property (
        @(posedge CLK) $rose(A3) && (B1 | B2) |-> (X == 1'b1)
    );

    // Rising B1 with A-group HIGH forces X HIGH.
    check_B1_rise_sets_X_when_Agroup_one: assert property (
        @(posedge CLK) $rose(B1) && (A1 | A2 | A3) |-> (X == 1'b1)
    );

    // Rising B2 with A-group HIGH forces X HIGH.
    check_B2_rise_sets_X_when_Agroup_one: assert property (
        @(posedge CLK) $rose(B2) && (A1 | A2 | A3) |-> (X == 1'b1)
    );

    ///// Output transition implications /////
    // If X falls, at least one input group OR must be LOW.
    check_X_fall_requires_group_zero: assert property (
        @(posedge CLK) $fell(X) |-> (~(A1 | A2 | A3) || ~(B1 | B2))
    );

    ///// Stability /////
    // If all inputs are stable, X must be stable.
    check_stable_inputs_hold_X_stable: assert property (
        @(posedge CLK) $stable(A1) && $stable(A2) && $stable(A3) && $stable(B1) && $stable(B2) |-> $stable(X)
    );
endmodule