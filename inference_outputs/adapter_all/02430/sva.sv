module counter_sva #(
    parameter int CTR_LEN = 27
) (
    input logic clk,
    input logic rst,
    input logic [7:0] value,
    input logic [CTR_LEN-1:0] ctr_q,
    input logic [CTR_LEN-1:0] ctr_d
);

    // Reset clears the counter and drives the default output value.
    check_reset_clears_counter_and_value: assert property (
        @(posedge clk) rst |=> (ctr_q == '0) && (value == 8'h00)
    );

    // The counter register loads the previous cycle's counter delta.
    check_counter_loads_delta: assert property (
        @(posedge clk) disable iff (rst)
        1'b1 |=> (ctr_q == $past(ctr_d))
    );

    // The delta register increments the previous cycle's counter.
    check_delta_increments_counter: assert property (
        @(posedge clk) disable iff (rst)
        1'b1 |=> (ctr_d == ($past(ctr_q) + 1'b1))
    );

    // A terminal count wraps the counter and drives the inverted MSB range.
    check_terminal_count_behavior: assert property (
        @(posedge clk) disable iff (rst)
        (ctr_q[CTR_LEN-1] == 1'b1) |=> (ctr_q == '0) && (value == ~$past(ctr_q[CTR_LEN-2:CTR_LEN-9]))
    );

    // A non-terminal count holds the counter and drives the MSB range directly.
    check_nonterminal_count_behavior: assert property (
        @(posedge clk) disable iff (rst)
        (ctr_q[CTR_LEN-1] == 1'b0) |=> (ctr_q == $past(ctr_q)) && (value == $past(ctr_q[CTR_LEN-2:CTR_LEN-9]))
    );

    // The output always matches the previous cycle's counter MSB range mapping.
    check_output_matches_previous_counter_range: assert property (
        @(posedge clk) disable iff (rst)
        1'b1 |=> (value == ($past(ctr_q[CTR_LEN-2:CTR_LEN-9]) ^ $past(ctr_q[CTR_LEN-1])))
    );

endmodule