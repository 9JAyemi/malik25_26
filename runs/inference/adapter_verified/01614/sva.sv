module up_down_counter_sva (
    input logic clk,
    input logic up_down,
    input logic load,
    input logic [3:0] input_data,
    input logic [3:0] Q
);

// Load captures input_data on the next cycle.
    check_load_captures_input: assert property (
        @(posedge clk) load |=> (Q == $past(input_data))
    );

// When not loading, Q increments by one when up_down is high.
    check_increment_when_up: assert property (
        @(posedge clk) (!load && up_down) |=> (Q == ($past(Q) + 4'd1))
    );

// When not loading, Q decrements by one when up_down is low.
    check_decrement_when_down: assert property (
        @(posedge clk) (!load && !up_down) |=> (Q == ($past(Q) - 4'd1))
    );

// Incrementing from 4'hF wraps Q to 4'h0.
    check_increment_wrap: assert property (
        @(posedge clk) (!load && up_down && (Q == 4'hF)) |=> (Q == 4'h0)
    );

// Decrementing from 4'h0 wraps Q to 4'hF.
    check_decrement_wrap: assert property (
        @(posedge clk) (!load && !up_down && (Q == 4'h0)) |=> (Q == 4'hF)
    );

endmodule
