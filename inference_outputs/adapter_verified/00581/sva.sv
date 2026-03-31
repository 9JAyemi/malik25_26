module pwm_out_sva (
    input logic        clk,
    input logic        reset_n,
    input logic        fifo_rdreq,
    input logic        fifo_empty,
    input logic [31:0] fifo_data,
    input logic        pwm_out_l,
    input logic        pwm_out_r
);

// fifo_rdreq is asserted only when the timer is at 0x800 and the FIFO is not empty.
    check_fifo_rdreq_only_on_timer800_nonempty: assert property (
        @(posedge clk) disable iff (!reset_n)
        (fifo_rdreq == (pwm_timer == 12'h800 && !fifo_empty))
    );

// When the timer reaches 0x800 and the FIFO is not empty, fifo_rdreq must be asserted.
    check_fifo_rdreq_on_timer800_nonempty: assert property (
        @(posedge clk) disable iff (!reset_n)
        (pwm_timer == 12'h800 && !fifo_empty) |-> (fifo_rdreq == 1'b1)
    );

// When the timer reaches 0x801 and a read request was issued in the previous cycle, fifo_rdreq must be deasserted.
    check_fifo_rdreq_deassert_on_timer801_after_request: assert property (
        @(posedge clk) disable iff (!reset_n)
        ($past(fifo_rdreq) && (pwm_timer == 12'h801)) |-> (fifo_rdreq == 1'b0)
    );

// When the timer reaches 0x801 and no read request was issued in the previous cycle, fifo_rdreq must remain deasserted.
    check_fifo_rdreq_hold_on_timer801_no_request: assert property (
        @(posedge clk) disable iff (!reset_n)
        (!$past(fifo_rdreq) && (pwm_timer == 12'h801)) |-> (fifo_rdreq == 1'b0)
    );

// When the timer reaches 0xFFF and a data sample was loaded in the previous cycle, the loaded sample must be repeated.
    check_sample_repeat_on_timerfff_after_load: assert property (
        @(posedge clk) disable iff (!reset_n)
        ($past(data_rdy) && (pwm_timer == 12'hfff)) |-> (audiodata_32 == $past(audiodata_32_p))
    );

// When the timer reaches 0xFFF and no data sample was loaded in the previous cycle, the loaded sample must hold its value.
    check_sample_hold_on_timerfff_no_load: assert property (
        @(posedge clk) disable iff (!reset_n)
        (!$past(data_rdy) && (pwm_timer == 12'hfff)) |-> (audiodata_32 == $past(audiodata_32))
    );

// pwm_out_l is high when the timer is less than or equal to the loaded left channel value.
    check_pwm_out_l_high_when_timer_le_left: assert property (
        @(posedge clk) disable iff (!reset_n)
        (pwm_timer <= audiodata_32[15:4]) |-> (pwm_out_l == 1'b1)
    );

// pwm_out_l is low when the timer is greater than the loaded left channel value.
    check_pwm_out_l_low_when_timer_gt_left: assert property (
        @(posedge clk) disable iff (!reset_n)
        (pwm_timer > audiodata_32[15:4]) |-> (pwm_out_l == 1'b0)
    );

// pwm_out_r is high when the timer is less than or equal to the loaded right channel value.
    check_pwm_out_r_high_when_timer_le_right: assert property (
        @(posedge clk) disable iff (!reset_n)
        (pwm_timer <= audiodata_32[31:20]) |-> (pwm_out_r == 1'b1)
    );

// pwm_out_r is low when the timer is greater than the loaded right channel value.
    check_pwm_out_r_low_when_timer_gt_right: assert property (
        @(posedge clk) disable iff (!reset_n)
        (pwm_timer > audiodata_32[31:20]) |-> (pwm_out_r == 1'b0)
    );

endmodule
