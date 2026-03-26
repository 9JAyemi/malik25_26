module sky130_fd_sc_ms__or4b_sva (
    input logic X,
    input logic A,
    input logic B,
    input logic C,
    input logic D_N
);

    // Use the formal global clock because this cell has no RTL clock.
    // X matches A OR B OR C OR NOT D_N.
    check_or_function_equivalence: assert property (
        @($global_clock) X == (A | B | C | ~D_N)
    );

    // Any active OR input drives X high.
    check_any_active_input_drives_high: assert property (
        @($global_clock) (A || B || C || !D_N) |-> X
    );

    // All inactive OR inputs drive X low.
    check_all_inactive_inputs_drive_low: assert property (
        @($global_clock) (!A && !B && !C && D_N) |-> !X
    );

    // X high implies at least one OR input is active.
    check_output_high_has_active_cause: assert property (
        @($global_clock) X |-> (A || B || C || !D_N)
    );

    // X low implies every OR input is inactive.
    check_output_low_only_when_all_inputs_inactive: assert property (
        @($global_clock) !X |-> (!A && !B && !C && D_N)
    );

endmodule