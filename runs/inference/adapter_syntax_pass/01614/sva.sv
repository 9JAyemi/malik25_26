module up_down_counter_sva (
    input logic clk,
    input logic up_down,
    input logic load,
    input logic [3:0] input_data,
    input logic [3:0] Q
);

    // Q matches the RTL next-state function.
    check_next_state_function: assert property (
        @(posedge clk)
        1'b1 |=> (Q == ($past(load) ? $past(input_data) : ($past(up_down) ? ($past(Q) + 4'd1) : ($past(Q) - 4'd1))))
    );

    // Load updates Q with input_data on the next cycle.
    check_load_updates_q: assert property (
        @(posedge clk)
        load |=> (Q == $past(input_data))
    );

    // With load low and up_down high, Q increments by one.
    check_increment_when_up: assert property (
        @(posedge clk)
        (!load && up_down) |=> (Q == ($past(Q) + 4'd1))
    );

    // With load low and up_down low, Q decrements by one.
    check_decrement_when_down: assert property (
        @(posedge clk)
        (!load && !up_down) |=> (Q == ($past(Q) - 4'd1))
    );

    // Increment wraps from 15 back to 0.
    check_increment_wraparound: assert property (
        @(posedge clk)
        (!load && up_down && (Q == 4'hF)) |=> (Q == 4'h0)
    );

    // Decrement wraps from 0 back to 15.
    check_decrement_wraparound: assert property (
        @(posedge clk)
        (!load && !up_down && (Q == 4'h0)) |=> (Q == 4'hF)
    );

endmodule