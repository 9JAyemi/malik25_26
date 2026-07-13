module sky130_fd_sc_hd__o22a_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2
);
    // Analysis: no clock or reset in RTL; pure combinational; X = (A1|A2) & (B1|B2). Use $global_clock for sampling.

    // Functional equivalence when inputs are known (no X/Z).
    check_function_when_known: assert property (
        @(posedge $global_clock) (!$isunknown({A1,A2,B1,B2})) |-> (X == ((A1 | A2) & (B1 | B2)))
    );

    // If X is HIGH then at least one A input and one B input must be HIGH.
    check_x_high_implies_groups_high: assert property (
        @(posedge $global_clock) (X == 1'b1) |-> ((A1 == 1'b1) || (A2 == 1'b1)) && ((B1 == 1'b1) || (B2 == 1'b1))
    );

    // If both A inputs are LOW then X must be LOW.
    check_a_group_zero_forces_x_zero: assert property (
        @(posedge $global_clock) (A1 == 1'b0 && A2 == 1'b0) |-> (X == 1'b0)
    );

    // If both B inputs are LOW then X must be LOW.
    check_b_group_zero_forces_x_zero: assert property (
        @(posedge $global_clock) (B1 == 1'b0 && B2 == 1'b0) |-> (X == 1'b0)
    );

    // If at least one A input and one B input are HIGH then X must be HIGH.
    check_groups_high_force_x_high: assert property (
        @(posedge $global_clock) ((A1 == 1'b1 || A2 == 1'b1) && (B1 == 1'b1 || B2 == 1'b1)) |-> (X == 1'b1)
    );

    // If all inputs are LOW then X must be LOW.
    check_all_zero_force_x_zero: assert property (
        @(posedge $global_clock) ({A1,A2,B1,B2} === 4'b0000) |-> (X === 1'b0)
    );

    // If all inputs are HIGH then X must be HIGH.
    check_all_one_force_x_one: assert property (
        @(posedge $global_clock) ({A1,A2,B1,B2} === 4'b1111) |-> (X === 1'b1)
    );

    // With stable inputs across a cycle, X must also be stable (no memory).
    check_stable_inputs_imply_stable_x: assert property (
        @(posedge $global_clock) $stable({A1,A2,B1,B2}) |-> $stable(X)
    );

    // If X is LOW then not both input groups can be HIGH simultaneously.
    check_x_low_implies_not_both_groups_high: assert property (
        @(posedge $global_clock) (X == 1'b0) |-> !(((A1 == 1'b1) || (A2 == 1'b1)) && ((B1 == 1'b1) || (B2 == 1'b1)))
    );
endmodule