module counter_sva (
    input logic clk,
    input logic reset,    // active-high asynchronous reset
    input logic enable,
    input logic [3:0] out
);

    ///// Reset behavior /////
    // On the first cycle after reset deasserts, out must be 0.
    check_out_zero_after_reset_fall: assert property (
        @(posedge clk) disable iff (reset) $fell(reset) |-> (out == 4'd0)
    );

    // If reset just deasserted and enable is 0, out stays 0 on the next cycle.
    check_zero_persists_one_cycle_if_no_enable_after_reset: assert property (
        @(posedge clk) disable iff (reset) ($fell(reset) && !enable) |=> (out == 4'd0)
    );

    // If reset just deasserted and enable is 1, out is still 0 before the increment occurs.
    check_out_zero_immediately_after_reset_fall_even_if_enable: assert property (
        @(posedge clk) disable iff (reset) ($fell(reset) && enable) |-> (out == 4'd0)
    );

    ///// Functional update constraints (robust to async reset between clocks) /////
    // If previous cycle had enable=1 and neither edge is in reset, out is either +1 or 0 (async reset).
    check_prev_enable1_next_out_plus_one_or_zero: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset) && !reset && $past(enable)) |-> 
            ((out == ($past(out) + 4'd1)[3:0]) || (out == 4'd0))
    );

    // If previous cycle had enable=0 and neither edge is in reset, out is either unchanged or 0 (async reset).
    check_prev_enable0_next_out_same_or_zero: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset) && !reset && !$past(enable)) |-> 
            ((out == $past(out)) || (out == 4'd0))
    );

    // With enable=1 in previous cycle and out was F, current out must be 0 (wrap or async reset).
    check_prev_enable1_wrap_from_F_to_0: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset) && !reset && $past(enable) && ($past(out) == 4'hF)) |-> 
            (out == 4'd0)
    );

    // If previous enable=0 and current out is non-zero (no reset at edges), it must equal the previous out.
    check_prev_enable0_nonzero_implies_stable: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset) && !reset && !$past(enable) && (out != 4'd0)) |-> 
            (out == $past(out))
    );

    // If previous enable=1 and current out is non-zero (no reset at edges), it must be previous +1 (mod 16).
    check_prev_enable1_nonzero_implies_plus_one: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset) && !reset && $past(enable) && (out != 4'd0)) |-> 
            (out == ($past(out) + 4'd1)[3:0])
    );

    // If previous enable=0 and previous out was 0 (no reset at edges), current out must be 0.
    check_prev_zero_holds_when_enable0: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset) && !reset && !$past(enable) && ($past(out) == 4'd0)) |-> 
            (out == 4'd0)
    );

endmodule