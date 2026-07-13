module up_down_counter_sva (
    input logic       clk,
    input logic       rst,
    input logic       up_down,
    input logic [2:0] count
);

    // A high reset clears the counter on the next clock.
    reset_clears_count: assert property (
        @(posedge clk) disable iff ($initstate)
        rst |=> (count == 3'b000)
    );

    // When up_down is high, the counter increments by one.
    check_count_increments: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        up_down |=> (count == ($past(count) + 3'b001))
    );

    // When up_down is low, the counter decrements by one.
    check_count_decrements: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        !up_down |=> (count == ($past(count) - 3'b001))
    );

    // Counting up wraps from 7 back to 0.
    check_wrap_up: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        (up_down && (count == 3'b111)) |=> (count == 3'b000)
    );

    // Counting down wraps from 0 back to 7.
    check_wrap_down: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        (!up_down && (count == 3'b000)) |=> (count == 3'b111)
    );

    // Outside reset, the counter value changes on every clock.
    check_count_changes_each_cycle: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        1'b1 |=> (count != $past(count))
    );

endmodule