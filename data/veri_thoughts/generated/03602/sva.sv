module sky130_fd_sc_hdll__o21bai_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1_N
);

    // Y matches the implemented NOT/OR/NAND/BUF logic.
    check_function_equation: assert property (
        @($global_clock) Y == ~((~B1_N) & (A1 | A2))
    );

    // If B1_N is high, the inverted B path forces Y high.
    check_b1n_high_forces_y_high: assert property (
        @($global_clock) B1_N |-> Y
    );

    // If both A inputs are low, the OR term is low and Y is high.
    check_a_inputs_low_force_y_high: assert property (
        @($global_clock) (!A1 && !A2) |-> Y
    );

    // With B1_N low and either A input high, Y must be low.
    check_active_b_and_or_term_drive_y_low: assert property (
        @($global_clock) (!B1_N && (A1 || A2)) |-> !Y
    );

    // A low Y only occurs when B1_N is low and the OR term is high.
    check_y_low_only_under_active_b_and_or_high: assert property (
        @($global_clock) (!Y) |-> (!B1_N && (A1 || A2))
    );

    // If B1_N is low and Y is high, both A inputs must be low.
    check_y_high_with_active_b_requires_a_inputs_low: assert property (
        @($global_clock) (!B1_N && Y) |-> (!A1 && !A2)
    );

endmodule