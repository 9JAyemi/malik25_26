module sky130_fd_sc_hd__a21oi_assertions (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1
);

    // Y equals the NOR of B1 and the A1/A2 AND term.
    check_boolean_function: assert property (
        @(posedge clk) Y == ~(B1 | (A1 & A2))
    );

    // B1 high forces Y low.
    check_b1_forces_y_low: assert property (
        @(posedge clk) B1 |-> (Y == 1'b0)
    );

    // A1 and A2 high force Y low.
    check_a1_a2_force_y_low: assert property (
        @(posedge clk) (A1 && A2) |-> (Y == 1'b0)
    );

    // With B1 low and either A input low, Y is high.
    check_b1_low_with_one_a_low_gives_y_high: assert property (
        @(posedge clk) (!B1 && (!A1 || !A2)) |-> (Y == 1'b1)
    );

endmodule