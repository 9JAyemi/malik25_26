module up_down_counter_sva (
    input logic clk,
    input logic up_down,
    input logic load,
    input logic [3:0] input_data,
    input logic [3:0] Q
);

    // Load captures input_data into Q on the next cycle.
    check_load_captures_input: assert property (
        @(posedge clk) load |=> (Q == $past(input_data))
    );

    // With load low and up_down high, Q increments by one.
    check_increment_when_up: assert property (
        @(posedge clk) (!load && up_down) |=> (Q == ($past(Q) + 4'd1))
    );

    // With load low and up_down low, Q decrements by one.
    check_decrement_when_down: assert property (
        @(posedge clk) (!load && !up_down) |=> (Q == ($past(Q) - 4'd1))
    );

    // With load low and up_down high, Q must change.
    check_increment_changes_q: assert property (
        @(posedge clk) (!load && up_down) |=> (Q != $past(Q))
    );

    // With load low and up_down low, Q must change.
    check_decrement_changes_q: assert property (
        @(posedge clk) (!load && !up_down) |=> (Q != $past(Q))
    );

    // With load low and up_down high, Q must not wrap below zero.
    check_increment_no_wrap_below_zero: assert property (
        @(posedge clk) (!load && up_down && ($past(Q) != 4'h0)) |=> (Q != 4'hF)
    );

    // With load low and up_down low, Q must not wrap above 15.
    check_decrement_no_wrap_above_max: assert property (
        @(posedge clk) (!load && !up_down && ($past(Q) != 4'hF)) |=> (Q != 4'h0)
    );

endmodule