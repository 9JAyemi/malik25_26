module sky130_fd_sc_ls__a32o_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic B2
);
    // Local combinational expression for the DUT function
    let a32o_expr = ((A3 & A1 & A2) | (B1 & B2));

    // X equals (A1 & A2 & A3) | (B1 & B2)
    check_functional_equivalence: assert property (
        @(posedge A1 or posedge A2 or posedge A3 or posedge B1 or posedge B2 or
          negedge A1 or negedge A2 or negedge A3 or negedge B1 or negedge B2)
        disable iff (1'b0)
        (X == a32o_expr)
    );

    // If the OR-of-ANDs is 1 then X is 1
    check_expr_high_implies_x_high: assert property (
        @(posedge A1 or posedge A2 or posedge A3 or posedge B1 or posedge B2 or
          negedge A1 or negedge A2 or negedge A3 or negedge B1 or negedge B2)
        disable iff (1'b0)
        a32o_expr |-> X
    );

    // If the OR-of-ANDs is 0 then X is 0
    check_expr_low_implies_x_low: assert property (
        @(posedge A1 or posedge A2 or posedge A3 or posedge B1 or posedge B2 or
          negedge A1 or negedge A2 or negedge A3 or negedge B1 or negedge B2)
        disable iff (1'b0)
        !a32o_expr |-> !X
    );

    // If X is 1 then at least one product term is 1
    check_x_high_has_cause: assert property (
        @(posedge A1 or posedge A2 or posedge A3 or posedge B1 or posedge B2 or
          negedge A1 or negedge A2 or negedge A3 or negedge B1 or negedge B2)
        disable iff (1'b0)
        X |-> ((A1 & A2 & A3) || (B1 & B2))
    );

    // If X is 0 then both product terms are 0
    check_x_low_means_no_terms: assert property (
        @(posedge A1 or posedge A2 or posedge A3 or posedge B1 or posedge B2 or
          negedge A1 or negedge A2 or negedge A3 or negedge B1 or negedge B2)
        disable iff (1'b0)
        !X |-> (!(A1 & A2 & A3) && !(B1 & B2))
    );

    // X changes iff the OR-of-ANDs changes (forward direction)
    check_expr_change_implies_x_change: assert property (
        @(posedge A1 or posedge A2 or posedge A3 or posedge B1 or posedge B2 or
          negedge A1 or negedge A2 or negedge A3 or negedge B1 or negedge B2)
        disable iff (1'b0)
        $changed(a32o_expr) |-> $changed(X)
    );

    // X changes iff the OR-of-ANDs changes (reverse direction)
    check_x_change_implies_expr_change: assert property (
        @(posedge A1 or posedge A2 or posedge A3 or posedge B1 or posedge B2 or
          negedge A1 or negedge A2 or negedge A3 or negedge B1 or negedge B2)
        disable iff (1'b0)
        $changed(X) |-> $changed(a32o_expr)
    );

    // If all inputs are stable over a cycle, X is stable over that cycle
    check_stability_with_stable_inputs: assert property (
        @(posedge A1 or posedge A2 or posedge A3 or posedge B1 or posedge B2 or
          negedge A1 or negedge A2 or negedge A3 or negedge B1 or negedge B2)
        disable iff (1'b0)
        ($stable(A1) && $stable(A2) && $stable(A3) && $stable(B1) && $stable(B2)) |-> $stable(X)
    );

    // Rising edge of the OR-of-ANDs causes a rising edge on X
    check_rise_follow: assert property (
        @(posedge A1 or posedge A2 or posedge A3 or posedge B1 or posedge B2 or
          negedge A1 or negedge A2 or negedge A3 or negedge B1 or negedge B2)
        disable iff (1'b0)
        $rose(a32o_expr) |-> $rose(X)
    );

    // Falling edge of the OR-of-ANDs causes a falling edge on X
    check_fall_follow: assert property (
        @(posedge A1 or posedge A2 or posedge A3 or posedge B1 or posedge B2 or
          negedge A1 or negedge A2 or negedge A3 or negedge B1 or negedge B2)
        disable iff (1'b0)
        $fell(a32o_expr) |-> $fell(X)
    );
endmodule