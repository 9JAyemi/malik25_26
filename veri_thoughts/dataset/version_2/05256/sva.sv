module dff_async_reset_sva (
    input logic q,
    input logic q_n,
    input logic d,
    input logic reset,
    input logic clk
);

    // q must be low whenever the active-low reset is asserted.
    check_reset_forces_q_low: assert property (
        @(posedge clk) !reset |-> (q == 1'b0)
    );

    // q_n must be high whenever the active-low reset is asserted.
    check_reset_forces_qn_high: assert property (
        @(posedge clk) !reset |-> (q_n == 1'b1)
    );

    // q_n must be the inverse of q during normal operation.
    check_qn_is_inverse_of_q: assert property (
        @(posedge clk) disable iff (!reset) (q_n == ~q)
    );

    // A sampled low reset keeps q low through the next clock sample.
    check_reset_keeps_q_low_next_cycle: assert property (
        @(posedge clk) !reset |=> (q == 1'b0)
    );

    // A rise on q must come from a prior clock with reset high and d high.
    check_q_rise_requires_prior_d_high: assert property (
        @(posedge clk) disable iff (!reset) $rose(q) |-> (($past(reset) == 1'b1) && ($past(d) == 1'b1))
    );

endmodule