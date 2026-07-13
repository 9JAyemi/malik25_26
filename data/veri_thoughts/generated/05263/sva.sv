module sky130_fd_sc_lp__and2b_sva (
    input logic clk,
    input logic X,
    input logic A_N,
    input logic B
);

    // X matches the implemented function (~A_N) & B.
    check_function: assert property (
        @(posedge clk) X == ((~A_N) & B)
    );

    // B low forces X low.
    check_b_low_forces_x_low: assert property (
        @(posedge clk) !B |-> !X
    );

    // A_N high forces X low.
    check_an_high_forces_x_low: assert property (
        @(posedge clk) A_N |-> !X
    );

    // A_N low with B high drives X high.
    check_selected_high: assert property (
        @(posedge clk) (!A_N && B) |-> X
    );

    // X high implies B is high and A_N is low.
    check_x_high_conditions: assert property (
        @(posedge clk) X |-> (B && !A_N)
    );

endmodule