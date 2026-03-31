module sky130_fd_sc_ms__o41a_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic A4,
    input logic B1
);

    // X must equal the OR of A1 through A4 gated by B1.
    check_x_matches_or_and_function: assert property (
        @(posedge clk) X == (B1 & (A1 | A2 | A3 | A4))
    );

    // B1 low forces X low.
    check_b1_low_forces_x_low: assert property (
        @(posedge clk) !B1 |-> !X
    );

    // All A inputs low force X low.
    check_all_a_low_forces_x_low: assert property (
        @(posedge clk) !(A1 | A2 | A3 | A4) |-> !X
    );

    // With B1 high, any asserted A input forces X high.
    check_b1_high_and_any_a_high_forces_x_high: assert property (
        @(posedge clk) (B1 & (A1 | A2 | A3 | A4)) |-> X
    );

    // A high X requires B1 to be high.
    check_x_high_requires_b1_high: assert property (
        @(posedge clk) X |-> B1
    );

    // A high X requires at least one A input to be high.
    check_x_high_requires_any_a_high: assert property (
        @(posedge clk) X |-> (A1 | A2 | A3 | A4)
    );

    // With B1 high, a low X means all A inputs are low.
    check_b1_high_and_x_low_requires_all_a_low: assert property (
        @(posedge clk) (B1 & !X) |-> !(A1 | A2 | A3 | A4)
    );

endmodule