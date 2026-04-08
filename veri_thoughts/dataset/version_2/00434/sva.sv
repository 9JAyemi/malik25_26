module sky130_fd_sc_ls__o41a_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic A4,
    input logic B1
);

    // X matches the OR-of-A inputs gated by B1.
    check_x_matches_or_and_function: assert property (
        @($global_clock) (X == ((A4 | A3 | A2 | A1) & B1))
    );

    // B1 low forces X low.
    check_b1_low_forces_x_low: assert property (
        @($global_clock) (B1 == 1'b0) |-> (X == 1'b0)
    );

    // All A inputs low force X low.
    check_all_a_low_forces_x_low: assert property (
        @($global_clock) ((A4 | A3 | A2 | A1) == 1'b0) |-> (X == 1'b0)
    );

    // X high requires B1 high.
    check_x_high_requires_b1_high: assert property (
        @($global_clock) (X == 1'b1) |-> (B1 == 1'b1)
    );

    // X high requires at least one A input high.
    check_x_high_requires_any_a_high: assert property (
        @($global_clock) (X == 1'b1) |-> ((A4 | A3 | A2 | A1) == 1'b1)
    );

    // A1 high with B1 high drives X high.
    check_a1_and_b1_drive_x_high: assert property (
        @($global_clock) ((A1 == 1'b1) && (B1 == 1'b1)) |-> (X == 1'b1)
    );

    // A2 high with B1 high drives X high.
    check_a2_and_b1_drive_x_high: assert property (
        @($global_clock) ((A2 == 1'b1) && (B1 == 1'b1)) |-> (X == 1'b1)
    );

    // A3 high with B1 high drives X high.
    check_a3_and_b1_drive_x_high: assert property (
        @($global_clock) ((A3 == 1'b1) && (B1 == 1'b1)) |-> (X == 1'b1)
    );

    // A4 high with B1 high drives X high.
    check_a4_and_b1_drive_x_high: assert property (
        @($global_clock) ((A4 == 1'b1) && (B1 == 1'b1)) |-> (X == 1'b1)
    );

endmodule