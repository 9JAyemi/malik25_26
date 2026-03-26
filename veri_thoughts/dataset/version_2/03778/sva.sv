module top_module_sva (
    input logic        clk,
    input logic        reset,
    input logic [7:0]  d,
    input logic [7:0]  in,
    input logic [7:0]  q,
    input logic [7:0]  rising_edge,
    input logic [7:0]  sum_output
);

    // q goes to all 1s one cycle after reset is sampled high.
    check_q_resets_to_ones: assert property (
        @(posedge clk)
        reset |=> (q == 8'hFF)
    );

    // q captures d one cycle after reset is sampled low.
    check_q_captures_d: assert property (
        @(posedge clk)
        (!reset) |=> (q == $past(d))
    );

    // rising_edge matches the implemented two-cycle delayed detection function of in.
    check_rising_edge_matches_function: assert property (
        @(posedge clk)
        1'b1 |-> ##2 (rising_edge == (($past(in,2) ^ ($past(in,2) >> 1)) & ($past(in,2) >> 1)))
    );

    // While not in reset, the MSB of rising_edge is always 0 after the pipeline delay.
    check_rising_edge_msb_zero: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |-> ##2 (rising_edge[7] == 1'b0)
    );

    // sum_output is the registered sum of the previous cycle's q and rising_edge.
    check_sum_output_matches_previous_sum: assert property (
        @(posedge clk)
        1'b1 |=> (sum_output == ($past(q) + $past(rising_edge)))
    );

endmodule