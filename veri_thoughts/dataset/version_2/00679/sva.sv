module binary_counter_sva (
    input logic clk,
    input logic rst,
    input logic en,
    input logic [3:0] count
);
    ///// Reset behavior /////
    // When rst is HIGH at a clock edge, count must be zero.
    check_reset_forces_zero: assert property (
        @(posedge clk) rst |-> (count == 4'd0)
    );

    // During reset, count is known and zero (no X/Z while rst is HIGH).
    check_known_zero_during_reset: assert property (
        @(posedge clk) rst |-> (!$isunknown(count) && count == 4'd0)
    );

    ///// Enable-driven counting (gated to cycles where rst is LOW at both ends) /////
    // With rst LOW in both cycles and en LOW in the previous cycle, count holds its value.
    check_hold_when_en_low: assert property (
        @(posedge clk) disable iff (rst)
            ($past(!rst,1,1'b0) && !rst && $past(!en,1,1'b0)) |-> (count == $past(count,1,4'h0))
    );

    // With rst LOW in both cycles and en HIGH in the previous cycle, count increments by 1 (mod 16).
    check_increment_when_en_high: assert property (
        @(posedge clk) disable iff (rst)
            ($past(!rst,1,1'b0) && !rst && $past(en,1,1'b0)) |-> (count == (($past(count,1,4'h0) + 4'd1) & 4'hF))
    );

    // With rst LOW in both cycles, if prior count was 4'hF and en was HIGH, next count wraps to 0.
    check_wrap_from_max: assert property (
        @(posedge clk) disable iff (rst)
            ($past(!rst,1,1'b0) && !rst && $past(en,1,1'b0) && ($past(count,1,4'h0) == 4'hF)) |-> (count == 4'h0)
    );
endmodule