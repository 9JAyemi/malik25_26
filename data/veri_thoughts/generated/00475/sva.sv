module sky130_fd_sc_ms__a31oi_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1
);

    // Y matches the implemented AOI31 boolean function.
    check_boolean_function: assert property (
        @(posedge clk) Y == ~(B1 | (A1 & A2 & A3))
    );

    // A high B1 forces the NOR output low.
    check_b1_forces_y_low: assert property (
        @(posedge clk) (B1 == 1'b1) |-> (Y == 1'b0)
    );

    // With B1 low, all three A inputs high force Y low.
    check_all_a_high_force_y_low: assert property (
        @(posedge clk) ((B1 == 1'b0) && (A1 == 1'b1) && (A2 == 1'b1) && (A3 == 1'b1)) |-> (Y == 1'b0)
    );

    // With B1 low, A1 low keeps Y high.
    check_a1_low_keeps_y_high: assert property (
        @(posedge clk) ((B1 == 1'b0) && (A1 == 1'b0)) |-> (Y == 1'b1)
    );

    // With B1 low, A2 low keeps Y high.
    check_a2_low_keeps_y_high: assert property (
        @(posedge clk) ((B1 == 1'b0) && (A2 == 1'b0)) |-> (Y == 1'b1)
    );

    // With B1 low, A3 low keeps Y high.
    check_a3_low_keeps_y_high: assert property (
        @(posedge clk) ((B1 == 1'b0) && (A3 == 1'b0)) |-> (Y == 1'b1)
    );

endmodule