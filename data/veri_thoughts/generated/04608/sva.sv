module counter_assertions (
    input logic       clk,
    input logic       reset,
    input logic [3:0] count,
    input logic       overflow
);

    // Synchronous reset clears both outputs.
    check_reset_clears_outputs: assert property (
        @(posedge clk) reset |=> (count == 4'd0) && (overflow == 1'b0)
    );

    // Count wraps to zero after reaching 15.
    check_wrap_count: assert property (
        @(posedge clk) disable iff (reset) (count == 4'd15) |=> (count == 4'd0)
    );

    // Overflow is asserted when the count wraps from 15.
    check_wrap_sets_overflow: assert property (
        @(posedge clk) disable iff (reset) (count == 4'd15) |=> (overflow == 1'b1)
    );

    // Count increments by one when below 15.
    check_increment_count: assert property (
        @(posedge clk) disable iff (reset) (count != 4'd15) |=> (count == ($past(count) + 4'd1))
    );

    // Overflow stays low on non-wrap increments.
    check_increment_clears_overflow: assert property (
        @(posedge clk) disable iff (reset) (count != 4'd15) |=> (overflow == 1'b0)
    );

endmodule