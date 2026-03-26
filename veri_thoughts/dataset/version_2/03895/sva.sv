module dffsr_assertions (
    input logic clk,
    input logic reset,
    input logic set,
    input logic d,
    input logic q,
    input logic qn
);

    // Reset forces q low and qn high.
    check_reset_values: assert property (
        @(posedge clk) reset |=> (q == 1'b0 && qn == 1'b1)
    );

    // Set forces q high and qn low when reset is not asserted.
    check_set_values: assert property (
        @(posedge clk) disable iff (reset) set |=> (q == 1'b1 && qn == 1'b0)
    );

    // Data 1 is captured when neither reset nor set is asserted.
    check_capture_d_high: assert property (
        @(posedge clk) disable iff (reset) (!set && d) |=> (q == 1'b1 && qn == 1'b0)
    );

    // Data 0 is captured when neither reset nor set is asserted.
    check_capture_d_low: assert property (
        @(posedge clk) disable iff (reset) (!set && !d) |=> (q == 1'b0 && qn == 1'b1)
    );

    // q and qn remain complementary after each non-reset clock.
    check_complementary_outputs: assert property (
        @(posedge clk) disable iff (reset) 1'b1 |=> (qn == ~q)
    );

endmodule