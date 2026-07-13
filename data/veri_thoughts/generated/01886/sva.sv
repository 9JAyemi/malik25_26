module up_down_counter_sva (
    input logic clk,
    input logic up_down,
    input logic [3:0] load,
    input logic [7:0] count
);

    // When load is non-zero, next count equals zero-extended load value.
    check_load_priority_value: assert property (
        @(posedge clk) (load != 4'd0) |=> (count == {4'b0000, $past(load)})
    );

    // When no load and up_down==1, next count increments by 1.
    check_increment_on_up: assert property (
        @(posedge clk) (load == 4'd0 && up_down == 1'b1) |=> (count == $past(count) + 8'd1)
    );

    // When no load and up_down==0, next count decrements by 1.
    check_decrement_on_down: assert property (
        @(posedge clk) (load == 4'd0 && up_down == 1'b0) |=> (count == $past(count) - 8'd1)
    );

    // On load, upper nibble of next count is zero.
    check_load_upper_nibble_zero: assert property (
        @(posedge clk) (load != 4'd0) |=> (count[7:4] == 4'b0000)
    );

    // On load, lower nibble of next count matches load.
    check_load_lower_nibble_matches: assert property (
        @(posedge clk) (load != 4'd0) |=> (count[3:0] == $past(load))
    );

    // With no load, next value changes by exactly +/-1 based on up_down.
    check_step_by_one_when_no_load: assert property (
        @(posedge clk) (load == 4'd0) |=> (count == $past(count) + ($past(up_down) ? 8'd1 : 8'hFF))
    );

    // Increment wrap-around: 0xFF -> 0x00 when no load and counting up.
    check_wrap_increment: assert property (
        @(posedge clk) (load == 4'd0 && up_down == 1'b1 && $past(count) == 8'hFF) |=> (count == 8'h00)
    );

    // Decrement wrap-around: 0x00 -> 0xFF when no load and counting down.
    check_wrap_decrement: assert property (
        @(posedge clk) (load == 4'd0 && up_down == 1'b0 && $past(count) == 8'h00) |=> (count == 8'hFF)
    );

    // Two consecutive no-load increments result in net +2 after two cycles.
    check_two_cycle_increment: assert property (
        @(posedge clk) (load == 4'd0 && up_down == 1'b1) ##1 (load == 4'd0 && up_down == 1'b1) |-> (count == $past(count,2) + 8'd2)
    );

    // Two consecutive no-load decrements result in net -2 after two cycles.
    check_two_cycle_decrement: assert property (
        @(posedge clk) (load == 4'd0 && up_down == 1'b0) ##1 (load == 4'd0 && up_down == 1'b0) |-> (count == $past(count,2) - 8'd2)
    );

endmodule