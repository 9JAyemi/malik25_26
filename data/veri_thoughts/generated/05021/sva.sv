module CSADD_sva (
    input logic clk,
    input logic rst,
    input logic x,
    input logic y,
    input logic ld,
    input logic sum,
    input logic sc
);

    // Reset holds sum low.
    check_reset_clears_sum: assert property (
        @(posedge clk) rst |-> (sum == 1'b0)
    );

    // Reset holds the carry state low.
    check_reset_clears_sc: assert property (
        @(posedge clk) rst |-> (sc == 1'b0)
    );

    // ld clears both state registers.
    check_load_clears_state: assert property (
        @(posedge clk) disable iff (rst)
        ld |=> (sum == 1'b0 && sc == 1'b0)
    );

    // A reset or load cycle leaves the sampled state cleared.
    check_state_zero_after_prior_clear: assert property (
        @(posedge clk) disable iff (rst)
        ($past(rst) || $past(ld)) |-> (sum == 1'b0 && sc == 1'b0)
    );

    // On active cycles, sum captures x ^ y ^ sc.
    check_add_updates_sum: assert property (
        @(posedge clk) disable iff (rst)
        (!ld) |=> (sum == $past(x ^ y ^ sc))
    );

    // On active cycles, sc captures the RTL carry equation.
    check_add_updates_sc: assert property (
        @(posedge clk) disable iff (rst)
        (!ld) |=> (sc == $past((y & sc) ^ (x & (y ^ sc))))
    );

    // With carry-in 0, the next state is a half-adder result.
    check_zero_carry_reduces_to_half_add: assert property (
        @(posedge clk) disable iff (rst)
        (!ld && (sc == 1'b0)) |=> ({sc, sum} == {$past(x & y), $past(x ^ y)})
    );

    // With carry-in 1, the next state uses XNOR for sum and OR for carry.
    check_one_carry_reduces_to_xnor_or: assert property (
        @(posedge clk) disable iff (rst)
        (!ld && (sc == 1'b1)) |=> ({sc, sum} == {$past(x | y), $past(~(x ^ y))})
    );

endmodule