module up_down_counter_sva (
    input logic clk,
    input logic up_down,
    input logic load,
    input logic reset,
    input logic [3:0] count,
    input logic [3:0] data_in
);

    // Reset forces the counter to zero.
    check_reset_forces_zero: assert property (
        @(posedge clk) reset |-> (count == 4'h0)
    );

    // Load updates count with data_in on the next clock.
    check_load_captures_data: assert property (
        @(posedge clk) disable iff (reset) load |=> (count == $past(data_in))
    );

    // Load has priority over increment when both are asserted.
    check_load_priority_over_increment: assert property (
        @(posedge clk) disable iff (reset) (load && up_down) |=> (count == $past(data_in))
    );

    // Without load, up_down high increments the counter.
    check_increment_operation: assert property (
        @(posedge clk) disable iff (reset) (!load && up_down) |=> (count == ($past(count) + 4'd1))
    );

    // Without load, up_down low decrements the counter.
    check_decrement_operation: assert property (
        @(posedge clk) disable iff (reset) (!load && !up_down) |=> (count == ($past(count) - 4'd1))
    );

    // Increment wraps from 4'hF to 4'h0.
    check_increment_wraparound: assert property (
        @(posedge clk) disable iff (reset) (!load && up_down && (count == 4'hF)) |=> (count == 4'h0)
    );

    // Decrement wraps from 4'h0 to 4'hF.
    check_decrement_wraparound: assert property (
        @(posedge clk) disable iff (reset) (!load && !up_down && (count == 4'h0)) |=> (count == 4'hF)
    );

endmodule