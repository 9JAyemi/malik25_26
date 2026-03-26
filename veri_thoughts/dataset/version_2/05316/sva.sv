module sky130_fd_sc_lp__a41o_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic A4,
    input logic B1
);

    // X matches the OR of B1 and the 4-input A AND term.
    check_x_matches_function: assert property (
        @(posedge clk) disable iff (1'b0)
        X == (B1 || (A1 && A2 && A3 && A4))
    );

    // A high B1 forces X high.
    check_b1_forces_x_high: assert property (
        @(posedge clk) disable iff (1'b0)
        B1 |-> X
    );

    // All A inputs high force X high.
    check_all_a_high_forces_x_high: assert property (
        @(posedge clk) disable iff (1'b0)
        (A1 && A2 && A3 && A4) |-> X
    );

    // With B1 low, any low A input forces X low.
    check_b1_low_and_missing_a_forces_x_low: assert property (
        @(posedge clk) disable iff (1'b0)
        (!B1 && (!A1 || !A2 || !A3 || !A4)) |-> !X
    );

    // If X is high without B1, all A inputs must be high.
    check_x_high_without_b1_requires_all_a_high: assert property (
        @(posedge clk) disable iff (1'b0)
        (X && !B1) |-> (A1 && A2 && A3 && A4)
    );

    // A low X requires B1 low and the A AND term low.
    check_x_low_requires_b1_low_and_a_term_low: assert property (
        @(posedge clk) disable iff (1'b0)
        !X |-> (!B1 && (!A1 || !A2 || !A3 || !A4))
    );

endmodule