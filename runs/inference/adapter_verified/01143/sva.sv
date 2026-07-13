module dual_edge_triggered_ff_sva (
    input logic clk,
    input logic d,
    input logic q
);

// On the first clock edge after a rising edge of d, q becomes 1 on the next negedge.
    check_q_one_after_d_rise: assert property (
        @(posedge clk) $rose(d) |=> ##1 (q == 1'b1)
    );

// On the first clock edge after a falling edge of d, q becomes 0 on the next negedge.
    check_q_zero_after_d_fall: assert property (
        @(posedge clk) $fell(d) |=> ##1 (q == 1'b0)
    );

// If d is 1 on a negedge, q is 1 on the next negedge.
    check_q_one_after_negedge_d_one: assert property (
        @(negedge clk) (d == 1'b1) |=> ##1 (q == 1'b1)
    );

// If d is 0 on a negedge, q is 0 on the next negedge.
    check_q_zero_after_negedge_d_zero: assert property (
        @(negedge clk) (d == 1'b0) |=> ##1 (q == 1'b0)
    );

endmodule
