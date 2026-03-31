module up_down_counter_sva (
    input logic clk,
    input logic load,
    input logic up_down,
    input logic [2:0] out
);

    // Load clears the counter on the next cycle.
    check_load_clears_counter: assert property (
        @(posedge clk) load |=> (out == 3'b000)
    );

    // Load has priority over up_down when both are asserted.
    check_load_priority_over_up_down: assert property (
        @(posedge clk) (load && up_down) |=> (out == 3'b000)
    );

    // When not loading and up_down is high, the counter increments.
    check_increment_when_up_down: assert property (
        @(posedge clk) (!load && up_down) |=> (out == ($past(out) + 3'b001))
    );

    // When not loading and up_down is low, the counter decrements.
    check_decrement_when_not_up_down: assert property (
        @(posedge clk) (!load && !up_down) |=> (out == ($past(out) - 3'b001))
    );

    // Incrementing from 7 wraps back to 0.
    check_increment_wrap_from_max: assert property (
        @(posedge clk) (!load && up_down && (out == 3'b111)) |=> (out == 3'b000)
    );

    // Decrementing from 0 wraps back to 7.
    check_decrement_wrap_from_min: assert property (
        @(posedge clk) (!load && !up_down && (out == 3'b000)) |=> (out == 3'b111)
    );

endmodule