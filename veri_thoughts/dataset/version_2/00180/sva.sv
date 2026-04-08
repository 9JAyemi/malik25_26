module up_down_counter_sva (
    input logic       clk,
    input logic       reset,
    input logic       control,
    input logic [3:0] count
);

    // Count is zero on the first cycle after reset is released.
    check_post_reset_zero: assert property (
        @(posedge clk) disable iff (reset)
        $past(reset) |-> (count == 4'b0000)
    );

    // Each active cycle updates count by one in the selected direction.
    check_next_state_update: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (count == ($past(control) ? ($past(count) + 4'd1) : ($past(count) - 4'd1)))
    );

    // control high causes an increment on the next clock.
    check_increment: assert property (
        @(posedge clk) disable iff (reset)
        control |=> (count == ($past(count) + 4'd1))
    );

    // control low causes a decrement on the next clock.
    check_decrement: assert property (
        @(posedge clk) disable iff (reset)
        !control |=> (count == ($past(count) - 4'd1))
    );

    // Incrementing from 4'hF wraps back to zero.
    check_increment_wrap: assert property (
        @(posedge clk) disable iff (reset)
        control && (count == 4'hF) |=> (count == 4'h0)
    );

    // Decrementing from zero wraps to 4'hF.
    check_decrement_wrap: assert property (
        @(posedge clk) disable iff (reset)
        !control && (count == 4'h0) |=> (count == 4'hF)
    );

endmodule