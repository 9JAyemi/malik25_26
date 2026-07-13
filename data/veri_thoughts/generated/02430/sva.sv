module counter_sva #(parameter CTR_LEN = 27) (
    input logic clk,
    input logic rst,
    input logic [7:0] value,
    input logic [CTR_LEN-1:0] ctr_q,
    input logic [CTR_LEN-1:0] ctr_d
);
    // Clock: clk; Reset: rst (active-high, synchronous).
    // Mixed logic: flopped counter (ctr_q), combinational next-state (ctr_d) and output map (value).

    ///// Next-state logic /////
    // ctr_d is defined as ctr_q + 1.
    check_ctr_d_is_q_plus_one: assert property (
        @(posedge clk) disable iff (rst) (ctr_d == (ctr_q + 1'b1))
    );

    // When ctr_q is all 1s, ctr_d wraps to 0.
    check_ctr_d_wraps_to_zero: assert property (
        @(posedge clk) disable iff (rst) (ctr_q == {CTR_LEN{1'b1}}) |-> (ctr_d == '0)
    );

    ///// Sequential update /////
    // When previous cycle was not in reset, ctr_q loads prior ctr_d.
    check_q_loads_prior_d: assert property (
        @(posedge clk) disable iff (rst) (!$past(rst)) |-> (ctr_q == $past(ctr_d))
    );

    // Counter increments by 1 every cycle out of reset.
    check_q_increments_each_cycle: assert property (
        @(posedge clk) disable iff (rst) (!$past(rst)) |-> (ctr_q == ($past(ctr_q) + 1'b1))
    );

    // If ctr_q is all 1s, next cycle wraps to 0 (no reset).
    check_wrap_to_zero_on_all_ones: assert property (
        @(posedge clk) disable iff (rst) (ctr_q == {CTR_LEN{1'b1}}) |=> (ctr_q == '0)
    );

    // On reset deassertion edge, ctr_q loads prior ctr_d.
    check_q_on_reset_fall_loads_prior_d: assert property (
        @(posedge clk) disable iff (rst) $fell(rst) |-> (ctr_q == $past(ctr_d))
    );

    ///// Output mapping /////
    // value equals selected slice XORed with MSB mask.
    check_value_matches_xor_map: assert property (
        @(posedge clk) disable iff (rst) (value ^ ctr_q[CTR_LEN-2:CTR_LEN-9]) == {8{ctr_q[CTR_LEN-1]}}
    );

    // If MSB is 0, value equals the selected slice.
    check_value_when_msb0: assert property (
        @(posedge clk) disable iff (rst) (ctr_q[CTR_LEN-1] == 1'b0) |-> (value == ctr_q[CTR_LEN-2:CTR_LEN-9])
    );

    // If MSB is 1, value equals bitwise-not of the selected slice.
    check_value_when_msb1: assert property (
        @(posedge clk) disable iff (rst) (ctr_q[CTR_LEN-1] == 1'b1) |-> (value == ~ctr_q[CTR_LEN-2:CTR_LEN-9])
    );

    // value must be either the slice or its bitwise inverse every cycle.
    check_value_is_slice_or_inv: assert property (
        @(posedge clk) disable iff (rst) (value == ctr_q[CTR_LEN-2:CTR_LEN-9]) || (value == ~ctr_q[CTR_LEN-2:CTR_LEN-9])
    );
endmodule