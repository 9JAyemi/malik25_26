module four_input_and_gate_sva (
    input logic [1:0] A,
    input logic [1:0] B,
    input logic [1:0] C,
    input logic [1:0] D,
    input logic EN,
    input logic Y
);
    // Use a formal global clock since RTL is purely combinational and has no clock/reset.
    default clocking cb @(posedge $global_clock); endclocking

    ///// Functional equivalence /////
    // Y matches the exact combinational expression from the RTL.
    check_y_definition: assert property (
        Y === ((EN == 1'b1) && (A == 2'b11) && (B == 2'b10) && (C == 2'b01) && (D == 2'b00))
    );

    ///// Simple implications derived from the RTL /////
    // EN low forces Y low.
    check_en_low_forces_y0: assert property (
        (EN == 1'b0) |-> (Y == 1'b0)
    );
    // If A is not 2'b11, Y must be low.
    check_a_mismatch_forces_y0: assert property (
        (A != 2'b11) |-> (Y == 1'b0)
    );
    // If B is not 2'b10, Y must be low.
    check_b_mismatch_forces_y0: assert property (
        (B != 2'b10) |-> (Y == 1'b0)
    );
    // If C is not 2'b01, Y must be low.
    check_c_mismatch_forces_y0: assert property (
        (C != 2'b01) |-> (Y == 1'b0)
    );
    // If D is not 2'b00, Y must be low.
    check_d_mismatch_forces_y0: assert property (
        (D != 2'b00) |-> (Y == 1'b0)
    );

    ///// Biconditional checks /////
    // Y high implies all inputs match and EN is high.
    check_y_high_implies_conditions: assert property (
        (Y == 1'b1) |-> ((EN == 1'b1) && (A == 2'b11) && (B == 2'b10) && (C == 2'b01) && (D == 2'b00))
    );
    // When EN and all inputs match, Y must be high.
    check_conditions_imply_y_high: assert property (
        ((EN == 1'b1) && (A == 2'b11) && (B == 2'b10) && (C == 2'b01) && (D == 2'b00)) |-> (Y == 1'b1)
    );

    ///// Edge-based sanity checks /////
    // A rising edge on Y can only occur when EN and all inputs match.
    check_y_rise_implies_conditions: assert property (
        $rose(Y) |-> ((EN == 1'b1) && (A == 2'b11) && (B == 2'b10) && (C == 2'b01) && (D == 2'b00))
    );
    // A falling edge on Y implies at least one condition is now false.
    check_y_fall_implies_any_condition_false: assert property (
        $fell(Y) |-> ((EN != 1'b1) || (A != 2'b11) || (B != 2'b10) || (C != 2'b01) || (D != 2'b00))
    );

endmodule