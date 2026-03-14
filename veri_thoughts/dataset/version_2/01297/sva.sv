module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic select,
    input logic [7:0] sum
);
    ///// Reset behavior (synchronous active-high) /////
    // After a reset cycle, sum must be zero.
    check_sum_zero_after_prev_reset: assert property (
        @(posedge clk) disable iff (reset)
            ($past(reset) == 1'b1) |-> (sum == 8'h00)
    );

    ///// Functional behavior (registered one-cycle adder) /////
    // When not previously in reset, sum equals last cycle's a + b (8-bit wrap).
    check_sum_from_prev_inputs: assert property (
        @(posedge clk) disable iff (reset)
            ($past(reset) == 1'b0) |-> (sum == ($past(a) + $past(b)))
    );

    // On reset deassertion this cycle, sum remains zero (was cleared last cycle).
    check_sum_zero_on_reset_fall: assert property (
        @(posedge clk) disable iff (reset)
            $fell(reset) |-> (sum == 8'h00)
    );

    // Adding zero on b (prev cycle) passes a through.
    check_sum_prev_b_zero: assert property (
        @(posedge clk) disable iff (reset)
            (($past(reset) == 1'b0) && ($past(b) == 8'h00)) |-> (sum == $past(a))
    );

    // Adding zero on a (prev cycle) passes b through.
    check_sum_prev_a_zero: assert property (
        @(posedge clk) disable iff (reset)
            (($past(reset) == 1'b0) && ($past(a) == 8'h00)) |-> (sum == $past(b))
    );

    // LSB of sum equals XOR of LSBs of a and b from previous cycle.
    check_lsb_xor: assert property (
        @(posedge clk) disable iff (reset)
            ($past(reset) == 1'b0) |-> (sum[0] == ($past(a[0]) ^ $past(b[0])))
    );

    // Example overflow: FF + 01 wraps to 00 (prev cycle operands).
    check_overflow_ff_plus_01_wrap: assert property (
        @(posedge clk) disable iff (reset)
            (($past(reset) == 1'b0) && ($past(a) == 8'hFF) && ($past(b) == 8'h01)) |-> (sum == 8'h00)
    );

    // Example overflow: 80 + 80 wraps to 00 (prev cycle operands).
    check_overflow_80_plus_80_wrap: assert property (
        @(posedge clk) disable iff (reset)
            (($past(reset) == 1'b0) && ($past(a) == 8'h80) && ($past(b) == 8'h80)) |-> (sum == 8'h00)
    );

    // When operands are equal (prev cycle), sum equals 2*a (8-bit wrap).
    check_double_when_equal_operands: assert property (
        @(posedge clk) disable iff (reset)
            (($past(reset) == 1'b0) && ($past(a) == $past(b))) |-> (sum == ($past(a) + $past(a)))
    );

    // Changing select does not affect computed sum (both branches are identical).
    check_select_toggle_irrelevant: assert property (
        @(posedge clk) disable iff (reset)
            (($past(reset) == 1'b0) && $changed(select)) |-> (sum == ($past(a) + $past(b)))
    );
endmodule