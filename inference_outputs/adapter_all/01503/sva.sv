module fsm_rising_edge_counter_sva (
    input logic clk,
    input logic in,
    input logic [2:0] count,
    input logic d_last,
    input logic [1:0] state
);

    localparam logic [1:0] IDLE  = 2'b00;
    localparam logic [1:0] COUNT = 2'b01;

    // IDLE holds when the previous input was high.
    check_idle_holds_on_high: assert property (
        @(posedge clk) disable iff (1'b0)
        (state == IDLE && d_last) |=> (state == IDLE && count == $past(count))
    );

    // IDLE holds when the previous input was low.
    check_idle_holds_on_low: assert property (
        @(posedge clk) disable iff (1'b0)
        (state == IDLE && !d_last) |=> (state == IDLE && count == $past(count))
    );

    // COUNT holds when the previous input was high.
    check_count_holds_on_high: assert property (
        @(posedge clk) disable iff (1'b0)
        (state == COUNT && d_last) |=> (state == COUNT && count == $past(count))
    );

    // COUNT increments when the previous input was low and count was below 4.
    check_count_increments_on_low: assert property (
        @(posedge clk) disable iff (1'b0)
        (state == COUNT && !d_last && (count != 3'd4)) |=> (state == COUNT && count == ($past(count) + 3'd1))
    );

    // COUNT returns to IDLE when the previous input was low and count was 4.
    check_count_returns_to_idle_on_low: assert property (
        @(posedge clk) disable iff (1'b0)
        (state == COUNT && !d_last && (count == 3'd4)) |=> (state == IDLE && count == 3'd0)
    );

    // d_last reflects the previous value of in.
    check_d_last_tracks_in: assert property (
        @(posedge clk) disable iff (1'b0)
        1'b1 |=> (d_last == $past(in))
    );

endmodule