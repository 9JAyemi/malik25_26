module counter_3bit_sva (
    input logic clk,
    input logic reset,
    input logic load,
    input logic [2:0] input_value,
    input logic [2:0] count
);

    // A sampled low reset drives count to zero by the next clock.
    check_reset_drives_zero: assert property (
        @(posedge clk) !reset |=> (count == 3'b000)
    );

    // A high load causes count to take the previous cycle's input value.
    check_load_updates_count: assert property (
        @(posedge clk) disable iff (!reset)
        load |=> (count == $past(input_value))
    );

    // Load overrides wrap behavior when count is 7.
    check_load_priority_over_wrap: assert property (
        @(posedge clk) disable iff (!reset)
        (load && (count == 3'b111)) |=> (count == $past(input_value))
    );

    // Without load, a count of 7 wraps back to 0.
    check_wrap_from_max: assert property (
        @(posedge clk) disable iff (!reset)
        (!load && (count == 3'b111)) |=> (count == 3'b000)
    );

    // Without load, counts below 7 increment by one.
    check_increment_when_not_loaded: assert property (
        @(posedge clk) disable iff (!reset)
        (!load && (count != 3'b111)) |=> (count == ($past(count) + 3'b001))
    );

endmodule