module sky130_fd_sc_lp__o31a_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1
);

    // X must equal the OR of A1, A2, and A3 gated by B1.
    check_x_matches_o31a_function: assert property (
        @(posedge clk) X == ((A1 | A2 | A3) & B1)
    );

    // B1 low must force X low.
    check_b1_low_forces_x_low: assert property (
        @(posedge clk) !B1 |-> !X
    );

    // All A inputs low must force X low.
    check_all_a_inputs_low_force_x_low: assert property (
        @(posedge clk) (!A1 && !A2 && !A3) |-> !X
    );

    // A1 high with B1 high must drive X high.
    check_a1_and_b1_drive_x_high: assert property (
        @(posedge clk) (A1 && B1) |-> X
    );

    // A2 high with B1 high must drive X high.
    check_a2_and_b1_drive_x_high: assert property (
        @(posedge clk) (A2 && B1) |-> X
    );

    // A3 high with B1 high must drive X high.
    check_a3_and_b1_drive_x_high: assert property (
        @(posedge clk) (A3 && B1) |-> X
    );

    // X high requires B1 to be high.
    check_x_high_requires_b1_high: assert property (
        @(posedge clk) X |-> B1
    );

    // X high requires at least one A input to be high.
    check_x_high_requires_any_a_high: assert property (
        @(posedge clk) X |-> (A1 || A2 || A3)
    );

endmodule