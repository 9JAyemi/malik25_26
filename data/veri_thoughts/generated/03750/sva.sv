module ir_recieve_assertions (
    input logic        clk,
    input logic        rst,
    input logic        sda,
    input logic        recieve_status,
    input logic [10:0] recieved_data,
    input logic [1:0]  sda_reg,
    input logic        falling_edge,
    input logic        rising_edge,
    input logic [7:0]  cyc_cnt,
    input logic [7:0]  start_cnt,
    input logic [31:0] time_cnt,
    input logic [2:0]  start_bits,
    input logic        data_start
);

    // Active-low reset forces all state to its initialized value.
    check_reset_state: assert property (
        @(posedge clk)
        !rst |-> (start_bits      == 3'b000)  &&
                 (start_cnt       == 8'd0)    &&
                 (time_cnt        == 32'd0)   &&
                 (cyc_cnt         == 8'd0)    &&
                 (data_start      == 1'b0)    &&
                 (sda_reg         == 2'b11)   &&
                 (recieved_data   == 11'd0)   &&
                 (recieve_status  == 1'b0)
    );

    // The SDA synchronizer shifts in the sampled SDA value each clock.
    check_sda_shift_register: assert property (
        @(posedge clk) disable iff (!rst)
        (sda_reg[0] == $past(sda)) &&
        (sda_reg[1] == $past(sda_reg[0]))
    );

    // falling_edge is asserted only for the 2'b10 SDA history pattern.
    check_falling_edge_decode: assert property (
        @(posedge clk) disable iff (!rst)
        (falling_edge == (sda_reg == 2'b10))
    );

    // rising_edge is asserted only for the 2'b01 SDA history pattern.
    check_rising_edge_decode: assert property (
        @(posedge clk) disable iff (!rst)
        (rising_edge == (sda_reg == 2'b01))
    );

    // A qualifying falling edge sets the indexed start bit and increments start_cnt.
    check_start_capture_update: assert property (
        @(posedge clk) disable iff (!rst)
        ($past(falling_edge) && ($past(start_cnt) < 8'd3)) |->
            (start_cnt == ($past(start_cnt) + 8'd1)) &&
            (start_bits == ($past(start_bits) | (3'b001 << $past(start_cnt))))
    );

    // Without a qualifying falling edge, start_bits and start_cnt hold their values.
    check_start_capture_hold: assert property (
        @(posedge clk) disable iff (!rst)
        !($past(falling_edge) && ($past(start_cnt) < 8'd3)) |->
            (start_cnt == $past(start_cnt)) &&
            (start_bits == $past(start_bits))
    );

    // The timing state stays idle until all three start bits have been seen.
    check_timer_idle_before_start: assert property (
        @(posedge clk) disable iff (!rst)
        ($past(start_bits) != 3'b111) |->
            (time_cnt == $past(time_cnt)) &&
            (cyc_cnt == $past(cyc_cnt)) &&
            (data_start == $past(data_start))
    );

    // Before data_start, time_cnt increments up to 44500.
    check_preamble_timer_increment: assert property (
        @(posedge clk) disable iff (!rst)
        ($past(start_bits) == 3'b111 && !$past(data_start) && ($past(time_cnt) < 32'd44500)) |->
            (time_cnt == ($past(time_cnt) + 32'd1)) &&
            (cyc_cnt == $past(cyc_cnt)) &&
            (data_start == 1'b0)
    );

    // At 44500 counts, the preamble timer resets and data_start asserts.
    check_preamble_done_sets_data_start: assert property (
        @(posedge clk) disable iff (!rst)
        ($past(start_bits) == 3'b111 && !$past(data_start) && ($past(time_cnt) == 32'd44500)) |->
            (time_cnt == 32'd0) &&
            (cyc_cnt == $past(cyc_cnt)) &&
            (data_start == 1'b1)
    );

    // During data collection, time_cnt increments until the bit period completes.
    check_bit_timer_increment: assert property (
        @(posedge clk) disable iff (!rst)
        ($past(start_bits) == 3'b111 && $past(data_start) &&
         ($past(cyc_cnt) < 8'd11) && ($past(time_cnt) < 32'd89000)) |->
            (time_cnt == ($past(time_cnt) + 32'd1)) &&
            (cyc_cnt == $past(cyc_cnt)) &&
            (data_start == 1'b1)
    );

    // At 89000 counts, the bit timer resets and cyc_cnt increments.
    check_bit_timer_wrap_advances_cycle: assert property (
        @(posedge clk) disable iff (!rst)
        ($past(start_bits) == 3'b111 && $past(data_start) &&
         ($past(cyc_cnt) < 8'd11) && ($past(time_cnt) == 32'd89000)) |->
            (time_cnt == 32'd0) &&
            (cyc_cnt == ($past(cyc_cnt) + 8'd1)) &&
            (data_start == 1'b1)
    );

    // A falling edge in the valid sample window writes a 1 into the current bit.
    check_falling_edge_samples_one: assert property (
        @(posedge clk) disable iff (!rst)
        ($past(falling_edge) &&
         ($past(time_cnt) > 32'd30000) && ($past(time_cnt) < 32'd60000) &&
         ($past(cyc_cnt) < 8'd11)) |->
            (recieved_data == ($past(recieved_data) | (11'h001 << $past(cyc_cnt))))
    );

    // A rising edge in the valid sample window writes a 0 into the current bit.
    check_rising_edge_samples_zero: assert property (
        @(posedge clk) disable iff (!rst)
        ($past(rising_edge) &&
         ($past(time_cnt) > 32'd30000) && ($past(time_cnt) < 32'd60000) &&
         ($past(cyc_cnt) < 8'd11)) |->
            (recieved_data == ($past(recieved_data) & ~(11'h001 << $past(cyc_cnt))))
    );

    // Without a valid sample edge, recieved_data holds its value.
    check_data_hold_without_sample_edge: assert property (
        @(posedge clk) disable iff (!rst)
        !(($past(falling_edge) &&
           ($past(time_cnt) > 32'd30000) && ($past(time_cnt) < 32'd60000) &&
           ($past(cyc_cnt) < 8'd11)) ||
          ($past(rising_edge) &&
           ($past(time_cnt) > 32'd30000) && ($past(time_cnt) < 32'd60000) &&
           ($past(cyc_cnt) < 8'd11))) |->
            (recieved_data == $past(recieved_data))
    );

    // recieve_status reflects whether the previous recieved_data matched the fixed pattern.
    check_status_matches_previous_data: assert property (
        @(posedge clk) disable iff (!rst)
        (recieve_status == ((($past(recieved_data) == 11'b00011110101) ? 1'b1 : 1'b0)))
    );

endmodule