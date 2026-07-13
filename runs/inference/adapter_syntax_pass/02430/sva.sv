module counter_sva #(
    parameter CTR_LEN = 27
) (
    input logic clk,
    input logic rst,
    input logic [7:0] value,
    input logic [CTR_LEN-1:0] ctr_q,
    input logic [CTR_LEN-1:0] ctr_d
);

    // Reset clears the counter state.
    check_reset_clears_counter: assert property (
        @(posedge clk) rst |=> (ctr_q == {CTR_LEN{1'b0}})
    );

    // Reset drives the visible output to zero.
    check_reset_clears_visible_output: assert property (
        @(posedge clk) rst |=> (value == 8'h00)
    );

    // The counter state increments by one on each active clock.
    check_counter_state_increments: assert property (
        @(posedge clk) disable iff (rst)
        1'b1 |=> (ctr_q == ($past(ctr_q) + 1'b1))
    );

    // The visible output matches the RTL's conditional mapping.
    check_visible_output_matches_rtl: assert property (
        @(posedge clk) disable iff (rst)
        1'b1 |-> (value == (ctr_q[CTR_LEN-1] ? ~ctr_q[CTR_LEN-2:CTR_LEN-9] : ctr_q[CTR_LEN-2:CTR_LEN-9]))
    );

    // A terminal count wraps the counter state to zero.
    check_terminal_count_wraps: assert property (
        @(posedge clk) disable iff (rst)
        (ctr_q == {CTR_LEN{1'b1}}) |=> (ctr_q == {CTR_LEN{1'b0}})
    );

    // A terminal count drives the visible output to zero.
    check_terminal_count_clears_visible_output: assert property (
        @(posedge clk) disable iff (rst)
        (ctr_q == {CTR_LEN{1'b1}}) |=> (value == 8'h00)
    );

    // A non-terminal count preserves the visible output.
    check_nonterminal_count_preserves_visible_output: assert property (
        @(posedge clk) disable iff (rst)
        (ctr_q != {CTR_LEN{1'b1}}) |=> (value == $past(value))
    );

endmodule