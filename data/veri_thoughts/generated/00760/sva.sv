module sky130_fd_sc_hd__o32ai_sva (
    input logic clk,   // Assertion clock (DUT has no clock/reset)
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic B2
);
    // Analysis: No clock/reset in DUT; logic is purely combinational.
    // Function: Y = ~((A1|A2|A3) & (B1|B2)) = ((~A1 & ~A2 & ~A3) | (~B1 & ~B2)).

    // Local combinational reductions for readability
    wire a_or = (A1 | A2 | A3);
    wire b_or = (B1 | B2);
    wire y_func_andinv   = ~(a_or & b_or);
    wire y_func_demorgan = ((~A1 & ~A2 & ~A3) | (~B1 & ~B2));

    ///// Functional equivalence checks /////
    // Y must equal ~( (A1|A2|A3) & (B1|B2) ).
    check_function_equivalence_andinv: assert property (
        @(posedge clk) (Y === y_func_andinv)
    );

    // Y must equal ((~A1 & ~A2 & ~A3) | (~B1 & ~B2)).
    check_function_equivalence_demorgan: assert property (
        @(posedge clk) (Y === y_func_demorgan)
    );

    // The two equivalent forms of the function must agree.
    check_internal_forms_agree: assert property (
        @(posedge clk) (y_func_andinv === y_func_demorgan)
    );

    ///// Useful implications of the Boolean function /////
    // If all A-group inputs are 0, Y is 1.
    check_y_high_when_a_group_all_zero: assert property (
        @(posedge clk) (!a_or) |-> (Y === 1'b1)
    );

    // If all B-group inputs are 0, Y is 1.
    check_y_high_when_b_group_all_zero: assert property (
        @(posedge clk) (!b_or) |-> (Y === 1'b1)
    );

    // If both groups have at least one 1, Y is 0.
    check_y_low_when_both_groups_active: assert property (
        @(posedge clk) (a_or && b_or) |-> (Y === 1'b0)
    );

    // If only A-group has a 1 and B-group has none, Y is 1.
    check_y_high_when_only_a_active: assert property (
        @(posedge clk) (a_or && !b_or) |-> (Y === 1'b1)
    );

    // If only B-group has a 1 and A-group has none, Y is 1.
    check_y_high_when_only_b_active: assert property (
        @(posedge clk) (!a_or && b_or) |-> (Y === 1'b1)
    );

    ///// Consistency and stability /////
    // If inputs are stable across a cycle, Y must be stable.
    check_output_stable_when_inputs_stable: assert property (
        @(posedge clk) $stable({A1,A2,A3,B1,B2}) |-> $stable(Y)
    );

    // If Y is 0, both group ORs must be 1.
    check_y_low_implies_both_groups_active: assert property (
        @(posedge clk) (Y === 1'b0) |-> (a_or && b_or)
    );

    // If Y is 1, at least one group OR must be 0.
    check_y_high_implies_some_group_zero: assert property (
        @(posedge clk) (Y === 1'b1) |-> ((!a_or) || (!b_or))
    );

endmodule