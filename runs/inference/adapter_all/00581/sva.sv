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
    check_reset_clears_state: assert property (
        @(posedge clk) !reset_n |-> (pwm_timer == 12'd0) &&
                                 (fifo_rdreq == 1'b0) &&
                                 (audiodata_32 == 32'd0) &&
                                 (audiodata_32_p == 32'd0) &&
                                 (data_rdy == 1'b0)
    );

    // pwm_timer increments by one on each active clock.
    check_pwm_timer_increments: assert property (
        @(posedge clk) disable iff (!reset_n)
        1'b1 |=> (pwm_timer == ($past(pwm_timer) + 12'd1))
    );

    // fifo_rdreq is asserted on the 0x800 sample and only when the FIFO is not empty.
    check_fifo_rdreq_on_sample: assert property (
        @(posedge clk) disable iff (!reset_n)
        (pwm_timer == 12'h800 && fifo_empty == 1'b0) |=> (fifo_rdreq == 1'b1)
    );

    // fifo_rdreq is deasserted on the 0x801 sample and only when the prior request was high.
    check_fifo_rdreq_clears_on_sample: assert property (
        @(posedge clk) disable iff (!reset_n)
        (pwm_timer == 12'h801 && $past(fifo_rdreq) == 1'b1) |=> (fifo_rdreq == 1'b0)
    );

    // audiodata_32_p captures fifo_data on the 0x801 sample and only when the prior request was high.
    check_audiodata_p_captures_on_sample: assert property (
        @(posedge clk) disable iff (!reset_n)
        (pwm_timer == 12'h801 && $past(fifo_rdreq) == 1'b1) |=> (audiodata_32_p == $past(fifo_data))
    );

    // data_rdy is asserted on the 0x801 sample and only when the prior request was high.
    check_data_rdy_sets_on_sample: assert property (
        @(posedge clk) disable iff (!reset_n)
        (pwm_timer == 12'h801 && $past(fifo_rdreq) == 1'b1) |=> (data_rdy == 1'b1)
    );

    // audiodata_32 loads audiodata_32_p on the 0xFFF sample and only when data_rdy was high.
    check_audiodata_loads_on_hold: assert property (
        @(posedge clk) disable iff (!reset_n)
        (pwm_timer == 12'hfff && $past(data_rdy) == 1'b1) |=> (audiodata_32 == $past(audiodata_32_p))
    );

    // data_rdy is cleared on the 0xFFF sample and only when data_rdy was high.
    check_data_rdy_clears_on_hold: assert property (
        @(posedge clk) disable iff (!reset_n)
        (pwm_timer == 12'hfff && $past(data_rdy) == 1'b1) |=> (data_rdy == 1'b0)
    );

    // pwm_out_l is the compare result of pwm_timer against audiodata_32[15:4].
    check_pwm_out_l_compare: assert property (
        @(posedge clk) disable iff (!reset_n)
        pwm_out_l == ((pwm_timer <= audiodata_32[15:4]) ? 1'b1 :
                      (pwm_timer >  audiodata_32[15:4]) ? 1'b0 : 1'bx)
    );

    // pwm_out_r is the compare result of pwm_timer against audiodata_32[31:20].
    check_pwm_out_r_compare: assert property (
        @(posedge clk) disable iff (!reset_n)
        pwm_out_r == ((pwm_timer <= audiodata_32[31:20]) ? 1'b1 :
                      (pwm_timer >  audiodata_32[31:20]) ? 1'b0 : 1'bx)
    );

endmodule