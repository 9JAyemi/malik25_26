module dff_sr_sva (
    input logic clk,
    input logic d,
    input logic set,
    input logic reset,
    input logic q,
    input logic q_n
);

    // Clock: posedge clk.
    // Reset: synchronous active-high.
    // Behavior: reset has priority over set, then d is captured.

    // Reset drives q low and q_n high.
    check_reset_state: assert property (
        @(posedge clk) reset |=> (q == 1'b0 && q_n == 1'b1)
    );

    // Set drives q high and q_n low when reset is inactive.
    check_set_state: assert property (
        @(posedge clk) disable iff (reset) set |=> (q == 1'b1 && q_n == 1'b0)
    );

    // A low d is captured when set and reset are low.
    check_capture_zero: assert property (
        @(posedge clk) disable iff (reset) (!set && !d) |=> (q == 1'b0 && q_n == 1'b1)
    );

    // A high d is captured when set and reset are low.
    check_capture_one: assert property (
        @(posedge clk) disable iff (reset) (!set && d) |=> (q == 1'b1 && q_n == 1'b0)
    );

    // The outputs remain complementary after each clocked update.
    check_complementary_outputs: assert property (
        @(posedge clk) 1'b1 |=> (q_n == ~q)
    );

endmodule