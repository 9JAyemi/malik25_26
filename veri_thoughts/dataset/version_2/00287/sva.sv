module counter_sva (
    input logic clk,
    input logic rst,
    input logic en,
    input logic up,
    input logic [3:0] count
);

    // While reset is high, count stays at zero.
    check_reset_holds_zero: assert property (
        @(posedge clk) rst |-> (count == 4'b0000)
    );

    // A reset assertion clears count by the next sampled edge.
    check_reset_clears_count: assert property (
        @(posedge clk or posedge rst) rst |=> (count == 4'b0000)
    );

    // When enable is low, count holds its value.
    check_hold_when_disabled: assert property (
        @(posedge clk or posedge rst) disable iff (rst)
        (!en) |=> (count == $past(count))
    );

    // When enabled and counting up, count increments by one.
    check_increment_when_enabled_up: assert property (
        @(posedge clk or posedge rst) disable iff (rst)
        (en && up) |=> (count == ($past(count) + 4'h1))
    );

    // When enabled and counting down, count decrements by one.
    check_decrement_when_enabled_down: assert property (
        @(posedge clk or posedge rst) disable iff (rst)
        (en && !up) |=> (count == ($past(count) - 4'h1))
    );

    // Counting up wraps from 15 to 0.
    check_wrap_up_from_max: assert property (
        @(posedge clk or posedge rst) disable iff (rst)
        (en && up && count == 4'hF) |=> (count == 4'h0)
    );

    // Counting down wraps from 0 to 15.
    check_wrap_down_from_zero: assert property (
        @(posedge clk or posedge rst) disable iff (rst)
        (en && !up && count == 4'h0) |=> (count == 4'hF)
    );

endmodule