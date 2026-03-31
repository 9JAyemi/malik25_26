module sky130_fd_sc_hvl__lsbuflv2hv_clkiso_hlkg_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic SLEEP_B
);

// X matches the implemented combinational function.
    check_functional_equivalence: assert property (
        @(posedge clk) X == (SLEEP_B & A)
    );

// A low forces X low.
    check_a_low_forces_x_low: assert property (
        @(posedge clk) !A |-> !X
    );

// SLEEP_B low forces X low.
    check_sleepb_low_forces_x_low: assert property (
        @(posedge clk) !SLEEP_B |-> !X
    );

// With both inputs high, X must be high.
    check_both_inputs_high_drive_x_high: assert property (
        @(posedge clk) (A && SLEEP_B) |-> X
    );

// X high implies both inputs are high.
    check_x_high_requires_both_inputs_high: assert property (
        @(posedge clk) X |-> (A && SLEEP_B)
    );

endmodule
