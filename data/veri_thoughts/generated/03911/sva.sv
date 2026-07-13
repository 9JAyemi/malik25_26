module serial_rx_sva #(
    parameter int CLK_PER_BIT = 50,
    parameter int CTR_SIZE = $clog2(CLK_PER_BIT)
)(
    input logic clk,
    input logic rst,
    input logic rx,
    input logic [7:0] data,
    input logic new_data,
    input logic [CTR_SIZE-1:0] ctr_q,
    input logic [2:0] bit_ctr_q,
    input logic [7:0] data_q,
    input logic new_data_q,
    input logic [1:0] state_q,
    input logic rx_q
);

    localparam logic [1:0] IDLE      = 2'd0;
    localparam logic [1:0] WAIT_HALF = 2'd1;
    localparam logic [1:0] WAIT_FULL = 2'd2;
    localparam logic [1:0] WAIT_HIGH = 2'd3;

    localparam logic [CTR_SIZE-1:0] HALF_COUNT = (CLK_PER_BIT >> 1);
    localparam logic [CTR_SIZE-1:0] FULL_COUNT = (CLK_PER_BIT - 1);

    // Formal starts with reset asserted.
    init_reset_assumption: assume property (
        @(posedge clk) $initstate |-> rst
    );

    // data output mirrors the internal data register.
    check_data_output_mirror: assert property (
        @(posedge clk) disable iff (rst) data === data_q
    );

    // new_data output mirrors the internal pulse register.
    check_new_data_output_mirror: assert property (
        @(posedge clk) disable iff (rst) new_data === new_data_q
    );

    // Synchronous reset initializes state and counters.
    check_reset_state: assert property (
        @(posedge clk) rst |=> (ctr_q == '0) && (bit_ctr_q == 3'b0) && (new_data_q == 1'b0) && (state_q == IDLE)
    );

    // rx_q captures rx on each clock.
    check_rx_q_tracks_rx: assert property (
        @(posedge clk) disable iff (rst) rx_q === $past(rx)
    );

    // IDLE clears counters and keeps new_data low on the next cycle.
    check_idle_clears_counters: assert property (
        @(posedge clk) disable iff (rst) (state_q == IDLE) |=> (ctr_q == '0) && (bit_ctr_q == 3'b0) && (new_data_q == 1'b0)
    );

    // A low sampled rx in IDLE starts the half-bit wait.
    check_idle_to_wait_half: assert property (
        @(posedge clk) disable iff (rst) (state_q == IDLE) && (rx_q == 1'b0) |=> (state_q == WAIT_HALF) && (ctr_q == '0) && (bit_ctr_q == 3'b0)
    );

    // A high sampled rx in IDLE keeps the receiver idle.
    check_idle_stays_idle_on_high: assert property (
        @(posedge clk) disable iff (rst) (state_q == IDLE) && (rx_q == 1'b1) |=> (state_q == IDLE) && (ctr_q == '0) && (bit_ctr_q == 3'b0)
    );

    // WAIT_HALF increments the counter until the half-bit point.
    check_wait_half_counts: assert property (
        @(posedge clk) disable iff (rst)
        (state_q == WAIT_HALF) && (ctr_q != HALF_COUNT)
        |=> (state_q == WAIT_HALF) &&
            (ctr_q == $past(ctr_q) + 1'b1) &&
            (bit_ctr_q == $past(bit_ctr_q)) &&
            (new_data_q == 1'b0)
    );

    // WAIT_HALF moves to WAIT_FULL at the half-bit point.
    check_wait_half_to_wait_full: assert property (
        @(posedge clk) disable iff (rst)
        (state_q == WAIT_HALF) && (ctr_q == HALF_COUNT)
        |=> (state_q == WAIT_FULL) &&
            (ctr_q == '0) &&
            (bit_ctr_q == $past(bit_ctr_q)) &&
            (new_data_q == 1'b0)
    );

    // WAIT_FULL increments the counter between sampling points.
    check_wait_full_counts: assert property (
        @(posedge clk) disable iff (rst)
        (state_q == WAIT_FULL) && (ctr_q != FULL_COUNT)
        |=> (state_q == WAIT_FULL) &&
            (ctr_q == $past(ctr_q) + 1'b1) &&
            (bit_ctr_q == $past(bit_ctr_q)) &&
            (data_q === $past(data_q)) &&
            (new_data_q == 1'b0)
    );

    // A non-final sample shifts in rx_q and stays in WAIT_FULL.
    check_wait_full_shift_mid_bits: assert property (
        @(posedge clk) disable iff (rst)
        (state_q == WAIT_FULL) && (ctr_q == FULL_COUNT) && (bit_ctr_q != 3'd7)
        |=> (state_q == WAIT_FULL) &&
            (ctr_q == '0) &&
            (bit_ctr_q == $past(bit_ctr_q) + 1'b1) &&
            (data_q === { $past(rx_q), $past(data_q[7:1]) }) &&
            (new_data_q == 1'b0)
    );

    // The final sample shifts in rx_q, raises new_data, and enters WAIT_HIGH.
    check_wait_full_last_bit: assert property (
        @(posedge clk) disable iff (rst)
        (state_q == WAIT_FULL) && (ctr_q == FULL_COUNT) && (bit_ctr_q == 3'd7)
        |=> (state_q == WAIT_HIGH) &&
            (ctr_q == '0) &&
            (bit_ctr_q == 3'b0) &&
            (data_q === { $past(rx_q), $past(data_q[7:1]) }) &&
            (new_data_q == 1'b1)
    );

    // new_data is only asserted while waiting for rx to return high.
    check_new_data_only_in_wait_high: assert property (
        @(posedge clk) disable iff (rst) new_data_q |-> (state_q == WAIT_HIGH)
    );

    // new_data is a single-cycle pulse.
    check_new_data_single_cycle: assert property (
        @(posedge clk) disable iff (rst) new_data_q |=> (new_data_q == 1'b0)
    );

    // WAIT_HIGH holds until the sampled line goes high.
    check_wait_high_holds_on_low: assert property (
        @(posedge clk) disable iff (rst)
        (state_q == WAIT_HIGH) && (rx_q == 1'b0)
        |=> (state_q == WAIT_HIGH) &&
            (ctr_q == '0) &&
            (bit_ctr_q == 3'b0) &&
            (new_data_q == 1'b0)
    );

    // WAIT_HIGH returns to IDLE once the sampled line is high.
    check_wait_high_to_idle: assert property (
        @(posedge clk) disable iff (rst)
        (state_q == WAIT_HIGH) && (rx_q == 1'b1)
        |=> (state_q == IDLE) && (new_data_q == 1'b0)
    );

endmodule