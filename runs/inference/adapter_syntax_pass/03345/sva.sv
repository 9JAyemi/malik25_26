module sky130_fd_sc_hvl__a21oi_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1
);

    // Y matches the implemented A21OI function.
    check_function_equivalence: assert property (
        @(posedge clk) Y == ~(B1 | (A1 & A2))
    );

    // B1 high forces the NOR output low.
    check_b1_forces_y_low: assert property (
        @(posedge clk) B1 |-> !Y
    );

    // A1 and A2 high together force the AND term high and Y low.
    check_a1_a2_force_y_low: assert property (
        @(posedge clk) (A1 && A2) |-> !Y
    );

    // With B1 low and A1 low, the AND term is low and Y is high.
    check_b1_low_a1_low_y_high: assert property (
        @(posedge clk) (!B1 && !A1) |-> Y
    );

    // With B1 low and A2 low, the AND term is low and Y is high.
    check_b1_low_a2_low_y_high: assert property (
        @(posedge clk) (!B1 && !A2) |-> Y
    );

    // With B1 low and A1 high, the AND term is low and Y is high.
    check_b1_low_a1_high_y_high: assert property (
        @(posedge clk) (!B1 && A1) |-> Y
    );

    // With B1 low and A2 high, the AND term is low and Y is high.
    check_b1_low_a2_high_y_high: assert property (
        @(posedge clk) (!B1 && A2) |-> Y
    );

endmodule