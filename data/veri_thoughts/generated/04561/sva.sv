module counter_sva (
    input logic       clk,
    input logic       rst,
    input logic       en,
    input logic       ctrl,
    input logic [3:0] count
);

    // Active-high reset keeps count at zero.
    check_reset_clears_count: assert property (
        @(posedge clk) rst |-> (count == 4'b0000)
    );

    // Count holds its value when enable is low.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (rst)
        (!en) |=> (count == $past(count))
    );

    // Count increments by one when enabled and ctrl is low.
    check_increment_when_enabled: assert property (
        @(posedge clk) disable iff (rst)
        (en && !ctrl) |=> (count == ($past(count) + 4'd1))
    );

    // Count decrements by one when enabled and ctrl is high.
    check_decrement_when_enabled: assert property (
        @(posedge clk) disable iff (rst)
        (en && ctrl) |=> (count == ($past(count) - 4'd1))
    );

endmodule