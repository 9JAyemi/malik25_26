module sky130_fd_sc_lp__a21oi_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1
);

    // Y matches the implemented A21OI boolean function.
    check_y_boolean_function: assert property (
        @(posedge clk) Y == ~((A1 & A2) | B1)
    );

    // A high B1 input forces the NOR output low.
    check_b1_forces_y_low: assert property (
        @(posedge clk) B1 |-> (Y == 1'b0)
    );

    // A1 and A2 high together force the AND term high and Y low.
    check_a1_a2_force_y_low: assert property (
        @(posedge clk) (A1 && A2) |-> (Y == 1'b0)
    );

    // With B1 low and A1 low, Y must be high.
    check_b1_low_a1_low_force_y_high: assert property (
        @(posedge clk) (!B1 && !A1) |-> (Y == 1'b1)
    );

    // With B1 low and A2 low, Y must be high.
    check_b1_low_a2_low_force_y_high: assert property (
        @(posedge clk) (!B1 && !A2) |-> (Y == 1'b1)
    );

endmodule