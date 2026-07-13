module d_ff_sva (
    input logic clk,
    input logic reset,
    input logic d,
    input logic q,
    input logic q_n
);
    // q_n must be the logical inverse of q when not in reset.
    check_qn_is_inverse_of_q: assert property (
        @(posedge clk) disable iff (!reset) (q_n == ~q)
    );

    // If reset is LOW at this cycle, q must be 0 on the next cycle.
    check_reset_low_clears_q_next: assert property (
        @(posedge clk) (!reset) |=> (q == 1'b0)
    );

    // If reset was LOW on the previous cycle, q must be 0 now.
    check_prev_reset_low_q_is_zero_now: assert property (
        @(posedge clk) $past(!reset) |-> (q == 1'b0)
    );

    // If reset is LOW at this cycle, q_n must be 1 on the next cycle.
    check_reset_low_sets_qn_next: assert property (
        @(posedge clk) (!reset) |=> (q_n == 1'b1)
    );

    // If reset was LOW on the previous cycle, q_n must be 1 now.
    check_prev_reset_low_qn_is_one_now: assert property (
        @(posedge clk) $past(!reset) |-> (q_n == 1'b1)
    );

    // q and q_n must never be equal when not in reset.
    check_q_and_qn_never_equal: assert property (
        @(posedge clk) disable iff (!reset) (q != q_n)
    );
endmodule