module fsm_rising_edge_counter_sva (
    input logic clk,
    input logic in,
    input logic [2:0] count,
    input logic d_last,
    input logic [1:0] state
);

    localparam logic [1:0] IDLE  = 2'b00;
    localparam logic [1:0] COUNT = 2'b01;

    // d_last is the previous cycle's in value.
    check_d_last_tracks_in: assert property (
        @(posedge clk) 1'b1 |=> (d_last == $past(in))
    );

    // IDLE holds when the input is low.
    check_idle_holds_when_in_low: assert property (
        @(posedge clk) (state == IDLE && !in) |=> (state == IDLE)
    );

    // IDLE increments count to 0 on a rising input edge.
    check_idle_sets_count_on_rise: assert property (
        @(posedge clk) (state == IDLE && in && !d_last) |=> (state == COUNT && count == 3'd0)
    );

    // COUNT holds when the input is low.
    check_count_holds_when_in_low: assert property (
        @(posedge clk) (state == COUNT && !in) |=> (state == COUNT)
    );

    // COUNT increments count to 1 on a rising input edge below 4.
    check_count_increments_below_4: assert property (
        @(posedge clk) (state == COUNT && in && !d_last && (count != 3'd4)) |=> (state == COUNT && count == ($past(count) + 3'd1))
    );

    // COUNT returns to IDLE when the input is low or count reaches 4.
    check_count_returns_to_idle: assert property (
        @(posedge clk) (state == COUNT && (!in || (count == 3'd4))) |=> (state == IDLE)
    );

endmodule