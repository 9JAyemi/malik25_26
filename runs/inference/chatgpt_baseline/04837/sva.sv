module counter_assertions (
    input logic       clk,
    input logic       rst,
    input logic       en,
    input logic [1:0] count
);

    // While reset is low, count stays at zero.
    check_reset_holds_zero: assert property (
        @(posedge clk) disable iff ($initstate)
        !rst |-> (count == 2'b00)
    );

    // If enable was low on the prior cycle, count holds its value.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (!rst || $initstate)
        $past(rst) && !$past(en) |-> (count == $past(count))
    );

    // If enabled from 0 on the prior cycle, count increments to 1.
    check_increment_from_0: assert property (
        @(posedge clk) disable iff (!rst || $initstate)
        $past(rst) && $past(en) && ($past(count) == 2'b00) |-> (count == 2'b01)
    );

    // If enabled from 1 on the prior cycle, count increments to 2.
    check_increment_from_1: assert property (
        @(posedge clk) disable iff (!rst || $initstate)
        $past(rst) && $past(en) && ($past(count) == 2'b01) |-> (count == 2'b10)
    );

    // If enabled from 2 on the prior cycle, count increments to 3.
    check_increment_from_2: assert property (
        @(posedge clk) disable iff (!rst || $initstate)
        $past(rst) && $past(en) && ($past(count) == 2'b10) |-> (count == 2'b11)
    );

    // If enabled from 3 on the prior cycle, count wraps to 0.
    check_wrap_from_3: assert property (
        @(posedge clk) disable iff (!rst || $initstate)
        $past(rst) && $past(en) && ($past(count) == 2'b11) |-> (count == 2'b00)
    );

endmodule