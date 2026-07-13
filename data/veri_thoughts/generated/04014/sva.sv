module up_counter_sva (
    input logic       clk,
    input logic       reset,
    input logic       load,
    input logic [3:0] load_value,
    input logic [3:0] count
);

    // A low reset forces the counter to zero by the next sampled clock.
    check_reset_clears_count: assert property (
        @(posedge clk) (!reset) |=> (count == 4'b0000)
    );

    // A load cycle copies load_value into count.
    check_load_updates_count: assert property (
        @(posedge clk) disable iff (!reset)
        (load == 1'b1) |=> (count == $past(load_value))
    );

    // A non-load cycle increments count when it is not at maximum.
    check_increment_no_wrap: assert property (
        @(posedge clk) disable iff (!reset)
        ((load == 1'b0) && (count != 4'hF)) |=> (count == ($past(count) + 4'd1))
    );

    // A non-load cycle wraps count from 4'hF to 4'h0.
    check_increment_wraps_to_zero: assert property (
        @(posedge clk) disable iff (!reset)
        ((load == 1'b0) && (count == 4'hF)) |=> (count == 4'h0)
    );

    // Every active cycle follows the RTL next-state relation.
    check_next_state_relation: assert property (
        @(posedge clk) disable iff (!reset)
        1'b1 |=> (
            (($past(load) == 1'b1) && (count == $past(load_value))) ||
            (($past(load) == 1'b0) && (count == ($past(count) + 4'd1)))
        )
    );

endmodule