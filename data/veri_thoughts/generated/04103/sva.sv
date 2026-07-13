module top_module_sva (
    input logic       clk,
    input logic       reset,
    input logic [7:0] d,
    input logic [7:0] q
);

    // A clock edge with reset high drives q to the fixed reset value next cycle.
    check_reset_loads_5a: assert property (
        @(posedge clk) reset |=> (q == 8'h5A)
    );

    // When reset is low and stays low, q captures d from that clock edge.
    check_data_captures_when_not_reset: assert property (
        @(posedge clk) disable iff (reset) (!reset) |=> (q == $past(d))
    );

    // On the first cycle reset is asserted, q still reflects the prior captured data.
    check_first_reset_cycle_keeps_prior_data: assert property (
        @(posedge clk) disable iff ($initstate) (reset && !$past(reset)) |-> (q == $past(d))
    );

    // One cycle after reset is sampled high, q holds the reset constant.
    check_q_after_reset_cycle: assert property (
        @(posedge clk) disable iff ($initstate) $past(reset) |-> (q == 8'h5A)
    );

endmodule