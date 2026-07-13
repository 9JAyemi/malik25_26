module sync_counter_sva (
    input logic       clk,
    input logic       rst,
    input logic       load,
    input logic [3:0] data_in,
    input logic [3:0] count_out
);

    // A sampled reset forces the next sampled count to zero.
    check_reset_seen_last_cycle_clears_count: assert property (
        @(posedge clk) disable iff ($initstate)
            $past(rst) |-> (count_out == 4'b0000)
    );

    // A nonzero value after a load cycle must match the loaded data.
    check_loaded_nonzero_value_appears_next_cycle: assert property (
        @(posedge clk) disable iff (rst || $initstate)
            ($past(load) && (count_out != 4'b0000)) |-> (count_out == $past(data_in))
    );

    // A nonzero value after a non-load cycle must be the incremented count.
    check_incremented_nonzero_value_appears_next_cycle: assert property (
        @(posedge clk) disable iff (rst || $initstate)
            (!$past(load) && (count_out != 4'b0000)) |-> (count_out == ($past(count_out) + 4'b0001))
    );

    // Loading zero makes the next sampled count zero.
    check_zero_load_appears_next_cycle: assert property (
        @(posedge clk) disable iff (rst || $initstate)
            ($past(load) && ($past(data_in) == 4'b0000)) |-> (count_out == 4'b0000)
    );

    // Incrementing from 4'hF rolls the next sampled count to zero.
    check_rollover_appears_as_zero: assert property (
        @(posedge clk) disable iff (rst || $initstate)
            (!$past(load) && ($past(count_out) == 4'hF)) |-> (count_out == 4'b0000)
    );

    // The next sampled count matches load, increment, or a reset-driven zero.
    check_next_state_matches_rtl_choices: assert property (
        @(posedge clk) disable iff (rst || $initstate)
            (count_out == 4'b0000) ||
            ($past(load) && (count_out == $past(data_in))) ||
            (!$past(load) && (count_out == ($past(count_out) + 4'b0001)))
    );

endmodule