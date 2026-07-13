module sky130_fd_sc_ms__nand2b_sva (
    input logic clk,
    input logic Y,
    input logic A_N,
    input logic B
);

// Y matches the implemented NOT-OR function.
    check_function_equivalence: assert property (
        @(posedge clk) Y == ~(~B | A_N)
    );

// A_N high forces Y low.
    check_a_n_high_forces_y_low: assert property (
        @(posedge clk) A_N |-> !Y
    );

// B low forces Y low.
    check_b_low_forces_y_low: assert property (
        @(posedge clk) !B |-> !Y
    );

// A_N low and B high drive Y high.
    check_active_inputs_drive_y_high: assert property (
        @(posedge clk) (!A_N && B) |-> Y
    );

// Y high implies both inputs are in their active state.
    check_y_high_implies_active_inputs: assert property (
        @(posedge clk) Y |-> (!A_N && B)
    );

endmodule
