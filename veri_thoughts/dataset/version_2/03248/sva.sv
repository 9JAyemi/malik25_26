module top_module_sva (
    input logic       clk,
    input logic       reset,
    input logic [3:0] q,
    input logic [2:0] count_ones
);

    // While reset remains asserted across sampled clocks, both outputs stay zero.
    check_reset_holds_zero: assert property (
        @(posedge clk)
        (($past(reset) === 1'b1) && reset) |-> ((q == 4'b0000) && (count_ones == 3'b000))
    );

    // On the first sampled clock after reset deasserts, the visible state is still zero.
    check_reset_release_starts_zero: assert property (
        @(posedge clk) disable iff (reset)
        ($past(reset) === 1'b1) |-> ((q == 4'b0000) && (count_ones == 3'b000))
    );

    // On consecutive sampled non-reset clocks, any nonzero q must be the prior value plus one.
    check_counter_nonzero_is_increment: assert property (
        @(posedge clk) disable iff (reset)
        (($past(reset) === 1'b0) && (q != 4'h0)) |-> (q == ($past(q) + 4'd1))
    );

    // On consecutive sampled non-reset clocks, a prior maximum count wraps to zero.
    check_counter_wraps_from_max: assert property (
        @(posedge clk) disable iff (reset)
        (($past(reset) === 1'b0) && ($past(q) == 4'hf)) |-> (q == 4'h0)
    );

    // When q has no pair of high bits, count_ones matches the implemented 3-bit reversed slice.
    check_count_ones_no_pair: assert property (
        @(posedge clk) disable iff (reset)
        (($past(reset) === 1'b0) &&
         !((q[0] & q[1]) | (q[0] & q[2]) | (q[0] & q[3]) |
           (q[1] & q[2]) | (q[1] & q[3]) | (q[2] & q[3])))
        |-> (count_ones == {q[1], q[2], q[3]})
    );

    // When q has any pair of high bits, count_ones is that 3-bit reversed slice minus one.
    check_count_ones_with_pair: assert property (
        @(posedge clk) disable iff (reset)
        (($past(reset) === 1'b0) &&
         ((q[0] & q[1]) | (q[0] & q[2]) | (q[0] & q[3]) |
          (q[1] & q[2]) | (q[1] & q[3]) | (q[2] & q[3])))
        |-> (count_ones == ({q[1], q[2], q[3]} - 3'd1))
    );

endmodule