module sky130_fd_sc_lp__or2_sva (
    input logic X,
    input logic A,
    input logic B
);
    ///// Functional equivalence checks /////
    // X equals A|B when A rises.
    check_func_eq_on_A_posedge: assert property (
        @(posedge A) X == (A | B)
    );
    // X equals A|B when A falls.
    check_func_eq_on_A_negedge: assert property (
        @(negedge A) X == (A | B)
    );
    // X equals A|B when B rises.
    check_func_eq_on_B_posedge: assert property (
        @(posedge B) X == (A | B)
    );
    // X equals A|B when B falls.
    check_func_eq_on_B_negedge: assert property (
        @(negedge B) X == (A | B)
    );

    ///// Output behavior on input transitions /////
    // A rising forces X high.
    check_x_high_on_a_rise: assert property (
        @(posedge A) X == 1'b1
    );
    // B rising forces X high.
    check_x_high_on_b_rise: assert property (
        @(posedge B) X == 1'b1
    );
    // A falling with B low forces X low.
    check_x_low_on_a_fall_when_b_low: assert property (
        @(negedge A) (B == 1'b0) |-> (X == 1'b0)
    );
    // B falling with A low forces X low.
    check_x_low_on_b_fall_when_a_low: assert property (
        @(negedge B) (A == 1'b0) |-> (X == 1'b0)
    );
    // A falling with B high keeps X high.
    check_x_stays_high_on_a_fall_when_b_high: assert property (
        @(negedge A) (B == 1'b1) |-> (X == 1'b1)
    );
    // B falling with A high keeps X high.
    check_x_stays_high_on_b_fall_when_a_high: assert property (
        @(negedge B) (A == 1'b1) |-> (X == 1'b1)
    );

    ///// Output edge implications /////
    // If X rises, at least one input is high.
    check_x_rise_implies_input_high: assert property (
        @(posedge X) (A == 1'b1) || (B == 1'b1)
    );
    // If X falls, both inputs are low.
    check_x_fall_implies_inputs_low: assert property (
        @(negedge X) (A == 1'b0) && (B == 1'b0)
    );
endmodule