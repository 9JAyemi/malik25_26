module dff_async_reset_sva (
    input logic clk,
    input logic d,
    input logic rst,
    input logic q
);

    // Low rst implies low q at sampled clock edges.
    check_reset_low_implies_q_low: assert property (
        @(posedge clk)
        1'b1 |=> ((rst == 1'b1) || (q == 1'b0))
    );

    // A sampled low rst leaves q low on the next clock.
    check_reset_keeps_q_low_next_clock: assert property (
        @(posedge clk)
        (rst == 1'b0) |=> (q == 1'b0)
    );

    // With reset deasserted, sampled d=0 is captured by the next clock.
    check_capture_zero: assert property (
        @(posedge clk) disable iff (!rst)
        (d == 1'b0) |=> (q == 1'b0)
    );

    // Whenever q is high, the previous sampled d must have been high.
    check_q_high_has_prior_high_d: assert property (
        @(posedge clk) disable iff (!rst)
        1'b1 |=> ((q == 1'b0) || ($past(d) == 1'b1))
    );

endmodule