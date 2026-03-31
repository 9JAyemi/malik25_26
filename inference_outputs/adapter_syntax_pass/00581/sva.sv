module pwm_out_sva (
    input logic        clk,
    input logic        reset_n,
    input logic        fifo_rdreq,
    input logic        fifo_empty,
    input logic [31:0] fifo_data,
    input logic        pwm_out_l,
    input logic        pwm_out_r,
    input logic        data_rdy,
    input logic [11:0] pwm_timer,
    input logic [31:0] audiodata_32,
    input logic [31:0] audiodata_32_p
);

    // Reset clears all registered state.
    check_reset_state: assert property (
        @(posedge clk)
        !reset_n |-> ((pwm_timer == 12'd0) &&
                      (fifo_rdreq == 1'b0) &&
                      (audiodata_32 == 32'd0) &&
                      (audiodata_32_p == 32'd0) &&
                      (data_rdy == 1'b0))
    );

    // pwm_timer increments by one on each active clock.
    check_pwm_timer_increment: assert property (
        @(posedge clk) disable iff (!reset_n)
        1'b1 |=> (pwm_timer == ($past(pwm_timer) + 12'd1))
    );

    // fifo_rdreq is asserted on the cycle after pwm_timer reaches 0x800.
    check_fifo_rdreq_on_800: assert property (
        @(posedge clk) disable iff (!reset_n)
        (pwm_timer == 12'h800) |=> (fifo_rdreq == 1'b1)
    );

    // fifo_rdreq is deasserted on the cycle after pwm_timer reaches 0x801.
    check_fifo_rdreq_on_801: assert property (
        @(posedge clk) disable iff (!reset_n)
        (pwm_timer == 12'h801) |=> (fifo_rdreq == 1'b0)
    );

    // fifo_rdreq is deasserted on the cycle after pwm_timer reaches 0xFFF.
    check_fifo_rdreq_on_fff: assert property (
        @(posedge clk) disable iff (!reset_n)
        (pwm_timer == 12'hFFF) |=> (fifo_rdreq == 1'b0)
    );

    // fifo_rdreq is never asserted on cycles other than 0x800.
    check_fifo_rdreq_only_on_800: assert property (
        @(posedge clk) disable iff (!reset_n)
        (fifo_rdreq == 1'b1) |-> (pwm_timer == 12'h800)
    );

    // data_rdy is asserted on the cycle after pwm_timer reaches 0x801.
    check_data_rdy_on_801: assert property (
        @(posedge clk) disable iff (!reset_n)
        (pwm_timer == 12'h801) |=> (data_rdy == 1'b1)
    );

    // data_rdy is cleared on the cycle after pwm_timer reaches 0xFFF.
    check_data_rdy_on_fff: assert property (
        @(posedge clk) disable iff (!reset_n)
        (pwm_timer == 12'hFFF) |=> (data_rdy == 1'b0)
    );

    // data_rdy is never asserted on cycles other than 0x801.
    check_data_rdy_only_on_801: assert property (
        @(posedge clk) disable iff (!reset_n)
        (data_rdy == 1'b1) |-> (pwm_timer == 12'h801)
    );

    // audiodata_32_p captures fifo_data on the cycle after pwm_timer reaches 0x801.
    check_audiodata_p_capture: assert property (
        @(posedge clk) disable iff (!reset_n)
        (pwm_timer == 12'h801) |=> (audiodata_32_p == $past(fifo_data))
    );

    // audiodata_32 loads audiodata_32_p on the cycle after pwm_timer reaches 0xFFF.
    check_audiodata_load: assert property (
        @(posedge clk) disable iff (!reset_n)
        (pwm_timer == 12'hFFF) |=> (audiodata_32 == $past(audiodata_32_p))
    );

    // pwm_out_l is high when pwm_timer is less than or equal to the low nibble of audiodata_32.
    check_pwm_out_l_low_nibble: assert property (
        @(posedge clk) disable iff (!reset_n)
        (pwm_timer <= audiodata_32[15:4]) |-> (pwm_out_l == 1'b1)
    );

    // pwm_out_l is low when pwm_timer is greater than the low nibble of audiodata_32.
    check_pwm_out_l_high_nibble: assert property (
        @(posedge clk) disable iff (!reset_n)
        (pwm_timer > audiodata_32[15:4]) |-> (pwm_out_l == 1'b0)
    );

    // pwm_out_r is high when pwm_timer is less than or equal to the high nibble of audiodata_32.
    check_pwm_out_r_high_nibble: assert property (
        @(posedge clk) disable iff (!reset_n)
        (pwm_timer <= audiodata_32[31:20]) |-> (pwm_out_r == 1'b1)
    );

    // pwm_out_r is low when pwm_timer is greater than the high nibble of audiodata_32.
    check_pwm_out_r_low_nibble: assert property (
        @(posedge clk) disable iff (!reset_n)
        (pwm_timer > audiodata_32[31:20]) |-> (pwm_out_r == 1'b0)
    );

endmodule