module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [7:0] d,
    input logic a,
    input logic b,
    input logic c,
    input logic [7:0] q
);

// q is zero whenever reset is asserted.
    check_reset_clears_q: assert property (
        @(posedge clk) reset |-> (q == 8'h00)
    );

// When reset is high, the flip-flops hold their previous value.
    check_ff_holds_when_reset: assert property (
        @(posedge clk) reset |-> (q[3:0] == $past(q[3:0]))
    );

// When reset is high, the multiplexer output is zero.
    check_mux_zero_when_reset: assert property (
        @(posedge clk) reset |-> (q[7:4] == 4'h0)
    );

// When reset is high, q is zero because the multiplexer output is zero.
    check_q_zero_when_reset: assert property (
        @(posedge clk) reset |-> (q == 8'h00)
    );

// With reset low, q[7:4] is always zero (mux selects 0).
    check_upper_nibble_zero: assert property (
        @(posedge clk) disable iff (reset) (q[7:4] == 4'h0)
    );

// With reset low, q[3:0] equals the previous cycle's d when the counter wraps.
    check_ff_loads_d_on_wrap: assert property (
        @(posedge clk) disable iff (reset)
            ($past(!reset) && ($past(q[3:0]) == 4'b1111) && (q[3:0] == $past(d)))
    );

// With reset low, q[3:0] holds its previous value when the counter does not wrap.
    check_ff_holds_when_no_wrap: assert property (
        @(posedge clk) disable iff (reset)
            ($past(!reset) && ($past(q[3:0]) != 4'b1111) && (q[3:0] == $past(q[3:0])))
    );

// With reset low, q[3:0] is zero on the first cycle after reset deasserts.
    check_ff_zero_after_reset_release: assert property (
        @(posedge clk) disable iff (reset)
            ($past(reset) && (q[3:0] == 4'h0))
    );

// With reset low, q[3:0] is zero on the first cycle after a counter wrap.
    check_ff_zero_after_wrap: assert property (
        @(posedge clk) disable iff (reset)
            ($past(!reset) && ($past(q[3:0]) == 4'b1111) && (q[3:0] == 4'h0))
    );

endmodule
