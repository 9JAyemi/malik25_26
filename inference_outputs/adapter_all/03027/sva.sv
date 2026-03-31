module sky130_fd_sc_lp__o31a_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1
);

    // X matches the implemented OR-then-AND function.
    check_functional_equivalence: assert property (
        @(posedge clk) X == (B1 & (A1 | A2 | A3))
    );

    // B1 low forces X low.
    check_b1_low_forces_x_low: assert property (
        @(posedge clk) !B1 |-> !X
    );

    // All A inputs low force X low.
    check_all_a_low_forces_x_low: assert property (
        @(posedge clk) !(A1 | A2 | A3) |-> !X
    );

    // With B1 high, any A input high drives X high.
    check_b1_high_and_any_a_high_drives_x_high: assert property (
        @(posedge clk) (B1 & (A1 | A2 | A3)) |-> X
    );

    // X high requires B1 high and at least one A input high.
    check_x_high_requires_b1_and_any_a: assert property (
        @(posedge clk) X |-> (B1 & (A1 | A2 | A3))
    );

    // X high implies B1 is high.
    check_x_high_implies_b1_high: assert property (
        @(posedge clk) X |-> B1
    );

    // X high implies at least one A input is high.
    check_x_high_implies_any_a_high: assert property (
        @(posedge clk) X |-> (A1 | A2 | A3)
    );

endmodule