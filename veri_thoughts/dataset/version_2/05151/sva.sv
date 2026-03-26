module logic_gate_sva (
    input logic A1,
    input logic A2,
    input logic A3,
    input logic A4,
    input logic B1,
    input logic Y
);

    // No clock or reset exists in the RTL; sample on the formal global clock.

    // Y must equal the implemented combinational expression.
    check_y_matches_logic_function: assert property (
        @($global_clock) Y == ((A1 & A2 & A3 & A4) | B1)
    );

    // B1 high forces Y high.
    check_b1_forces_y_high: assert property (
        @($global_clock) B1 |-> Y
    );

    // All A inputs high force Y high.
    check_all_a_inputs_force_y_high: assert property (
        @($global_clock) (A1 & A2 & A3 & A4) |-> Y
    );

    // If neither input term is active, Y must be low.
    check_no_active_term_means_y_low: assert property (
        @($global_clock) (!B1 && !(A1 & A2 & A3 & A4)) |-> !Y
    );

    // If Y is high while B1 is low, all A inputs must be high.
    check_y_high_without_b1_requires_all_a_high: assert property (
        @($global_clock) (Y && !B1) |-> (A1 & A2 & A3 & A4)
    );

endmodule