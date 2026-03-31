module sky130_fd_sc_hvl__lsbuflv2hv_clkiso_hlkg_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic SLEEP_B
);

// X must match the implemented A&SLEEP_B AND function.
    check_functional_equivalence: assert property (
        @(posedge clk) X == (A & SLEEP_B)
    );

// When SLEEP_B is low, X must be low.
    check_sleep_forces_low: assert property (
        @(posedge clk) !SLEEP_B |-> (X == 1'b0)
    );

// When A is low, X must be low.
    check_a_low_forces_low: assert property (
        @(posedge clk) !A |-> (X == 1'b0)
    );

// When both A and SLEEP_B are high, X must be high.
    check_both_high_drive_high: assert property (
        @(posedge clk) (A && SLEEP_B) |-> (X == 1'b1)
    );

// A high X requires both A and SLEEP_B to be high.
    check_high_output_requires_both_high: assert property (
        @(posedge clk) X |-> (A && SLEEP_B)
    );

endmodule
