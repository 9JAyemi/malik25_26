module counter_sva (
    input logic clk,
    input logic rst,
    input logic [31:0] q
);
    // Clock: clk (posedge). Reset: rst (active-high, asynchronous). Sequential up-counter.

    // q must be 0 whenever rst is high at a clock edge.
    check_reset_forces_zero: assert property (
        @(posedge clk) rst |-> (q == 32'd0)
    );

    // q is 0 on a rising edge of rst observed at a clock edge.
    check_zero_on_reset_rise: assert property (
        @(posedge clk) $rose(rst) |-> (q == 32'd0)
    );

    // While rst stays high across cycles, q stays 0 and stable.
    check_zero_stable_while_reset: assert property (
        @(posedge clk) (rst && $past(rst)) |-> (q == 32'd0 && $past(q) == 32'd0)
    );

    // On a falling edge of rst observed at a clock edge, q becomes 1.
    check_q_one_on_reset_fall: assert property (
        @(posedge clk) disable iff (rst) $fell(rst) |-> (q == 32'd1)
    );

    // Immediately following a cycle with rst high, q at the next edge is 0 or 1.
    check_next_cycle_after_reset_range: assert property (
        @(posedge clk) rst |=> (q inside {32'd0, 32'd1})
    );

    // When rst is low, q equals either $past(q)+1 (normal increment) or 1 (if reset happened between edges).
    check_increment_or_one_when_rst_low: assert property (
        @(posedge clk) disable iff (rst) ($past(1'b1) && !rst) |-> (q == ($past(q) + 32'd1) || q == 32'd1)
    );

endmodule