module sky130_fd_sc_lp__a41oi_0_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic A4,
    input logic B1
);
    ///// Functional equivalence to RTL expression /////
    // Y matches the RTL Boolean expression at A1 rising edge.
    check_func_eq_on_A1_pos: assert property (
        @(posedge A1) Y == ((A1 & A2 & ~A3 & ~A4 & B1) | (A1 & A2 & ~A3 & ~A4 & ~B1))
    );
    // Y matches the RTL Boolean expression at A2 rising edge.
    check_func_eq_on_A2_pos: assert property (
        @(posedge A2) Y == ((A1 & A2 & ~A3 & ~A4 & B1) | (A1 & A2 & ~A3 & ~A4 & ~B1))
    );
    // Y matches the RTL Boolean expression at A3 rising edge.
    check_func_eq_on_A3_pos: assert property (
        @(posedge A3) Y == ((A1 & A2 & ~A3 & ~A4 & B1) | (A1 & A2 & ~A3 & ~A4 & ~B1))
    );
    // Y matches the RTL Boolean expression at A4 rising edge.
    check_func_eq_on_A4_pos: assert property (
        @(posedge A4) Y == ((A1 & A2 & ~A3 & ~A4 & B1) | (A1 & A2 & ~A3 & ~A4 & ~B1))
    );
    // Y matches the RTL Boolean expression at B1 rising edge.
    check_func_eq_on_B1_pos: assert property (
        @(posedge B1) Y == ((A1 & A2 & ~A3 & ~A4 & B1) | (A1 & A2 & ~A3 & ~A4 & ~B1))
    );

    ///// Direct implications from the logic /////
    // When Y rises, inputs must satisfy A1&A2&~A3&~A4.
    check_y_rise_requires_inputs: assert property (
        @(posedge Y) (A1 & A2 & ~A3 & ~A4)
    );
    // When Y falls, inputs cannot satisfy A1&A2&~A3&~A4.
    check_y_fall_requires_not_inputs: assert property (
        @(negedge Y) !(A1 & A2 & ~A3 & ~A4)
    );

    ///// Independence from B1 (Y does not change if only B1 changes) /////
    // At B1 rising edge, if A1..A4 are stable, Y must be stable.
    check_b1_posedge_no_effect: assert property (
        @(posedge B1) ((A1 == $past(A1)) && (A2 == $past(A2)) && (A3 == $past(A3)) && (A4 == $past(A4))) |-> (Y == $past(Y))
    );
    // At B1 falling edge, if A1..A4 are stable, Y must be stable.
    check_b1_negedge_no_effect: assert property (
        @(negedge B1) ((A1 == $past(A1)) && (A2 == $past(A2)) && (A3 == $past(A3)) && (A4 == $past(A4))) |-> (Y == $past(Y))
    );

endmodule