module binary_counter_sva (
    input logic        clk,
    input logic        reset,
    input logic        count_en,
    input logic [31:0] max_count,
    input logic [31:0] load_val,
    input logic        load,
    input logic        count_dir,
    input logic [31:0] count_out
);

    // Load writes load_val into count_out on the next clock, unless async reset clears it.
    check_load_updates_count: assert property (
        @(posedge clk) disable iff (reset)
        load |=> ((count_out == $past(load_val)) || (count_out == 32'd0))
    );

    // Load takes priority over counting when both controls are asserted.
    check_load_has_priority_over_count: assert property (
        @(posedge clk) disable iff (reset)
        (load && count_en) |=> ((count_out == $past(load_val)) || (count_out == 32'd0))
    );

    // Without load or count enable, count_out holds its value, unless async reset clears it.
    check_hold_when_idle: assert property (
        @(posedge clk) disable iff (reset)
        (!load && !count_en) |=> ((count_out == $past(count_out)) || (count_out == 32'd0))
    );

    // When counting up at max_count, the counter wraps to zero.
    check_count_up_wraps_to_zero: assert property (
        @(posedge clk) disable iff (reset)
        (!load && count_en && count_dir && (count_out == max_count)) |=> (count_out == 32'd0)
    );

    // When counting up below max_count, the counter increments by one, unless async reset clears it.
    check_count_up_increments: assert property (
        @(posedge clk) disable iff (reset)
        (!load && count_en && count_dir && (count_out != max_count))
        |=> ((count_out == ($past(count_out) + 32'd1)) || (count_out == 32'd0))
    );

    // When counting down from zero, the counter wraps to max_count, unless async reset clears it.
    check_count_down_wraps_to_max: assert property (
        @(posedge clk) disable iff (reset)
        (!load && count_en && !count_dir && (count_out == 32'd0))
        |=> ((count_out == $past(max_count)) || (count_out == 32'd0))
    );

    // When counting down above zero, the counter decrements by one, unless async reset clears it.
    check_count_down_decrements: assert property (
        @(posedge clk) disable iff (reset)
        (!load && count_en && !count_dir && (count_out != 32'd0))
        |=> ((count_out == ($past(count_out) - 32'd1)) || (count_out == 32'd0))
    );

endmodule