module up_down_counter_sva (
    input logic clk,
    input logic load,
    input logic up_down,
    input logic [2:0] out
);

    // Load clears the counter on the next clock.
    check_load_clears_out: assert property (
        @(posedge clk) load |=> (out == 3'b000)
    );

    // Load has priority over the up/down select.
    check_load_priority_over_count: assert property (
        @(posedge clk) (load && up_down) |=> (out == 3'b000)
    );

    // Count up increments the counter when load is low.
    check_count_up_increments_out: assert property (
        @(posedge clk) (!load && up_down) |=> (out == ($past(out) + 3'b001))
    );

    // Count down decrements the counter when load is low.
    check_count_down_decrements_out: assert property (
        @(posedge clk) (!load && !up_down) |=> (out == ($past(out) - 3'b001))
    );

    // The counter wraps from 7 up to 0.
    check_count_up_wraps_from_7_to_0: assert property (
        @(posedge clk) (!load && up_down && (out == 3'b111)) |=> (out == 3'b000)
    );

    // The counter wraps from 0 down to 7.
    check_count_down_wraps_from_0_to_7: assert property (
        @(posedge clk) (!load && !up_down && (out == 3'b000)) |=> (out == 3'b111)
    );

endmodule