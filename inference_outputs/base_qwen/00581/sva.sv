module pwm_out_sva (
    input logic clk,
    input logic reset_n,
    output logic fifo_rdreq,
    input logic fifo_empty,
    input logic [31:0] fifo_data,
    output logic pwm_out_l,
    output logic pwm_out_r
);
    // FIFO read request should only be asserted when FIFO is not empty
    fifo_read_request: assert property (
        @(posedge clk) disable iff (!reset_n) fifo_rdreq |-> !fifo_empty
    );

    // FIFO read request should be deasserted after data is read
    fifo_read_request_deassert: assert property (
        @(posedge clk) disable iff (!reset_n) fifo_rdreq |-> fifo_empty
    );

    // PWM timer should increment on every clock cycle
    pwm_timer_increment: assert property (
        @(posedge clk) disable iff (!reset_n) pwm_timer |-> pwm_timer + 1'b1
    );

    // PWM timer should reset to 0 on reset
    pwm_timer_reset: assert property (
        @(posedge clk) disable iff (!reset_n) pwm_timer |-> 0
    );

    // PWM output left should be 1 when timer is less than or equal to the upper 12 bits of audio data
    pwm_out_l_check: assert property (
        @(posedge clk) disable iff (!reset_n) pwm_timer <= fifo_data[15:4] |-> pwm_out_l == 1'b1
    );

    // PWM output left should be 0 when timer is greater than the upper 12 bits of audio data
    pwm_out_l_check_2: assert property (
        @(posedge clk) disable iff (!reset_n) pwm_timer > fifo_data[15:4] |-> pwm_out_l == 1'b0
    );

    // PWM output right should be 1 when timer is less than or equal to the upper 12 bits of audio data
    pwm_out_r_check: assert property (
        @(posedge clk) disable iff (!reset_n) pwm_timer <= fifo_data[31:20] |-> pwm_out_r == 1'b1
    );

    // PWM output right should be 0 when timer is greater than the upper 12 bits of audio data
    pwm_out_r_check_2: assert property (
        @(posedge clk) disable iff (!reset_n) pwm_timer > fifo_data[31:20] |-> pwm_out_r == 1'b0
    );

    // Audio data should be updated when data is ready
    audio_data_update: assert property (
        @(posedge clk) disable iff (!reset_n) data_rdy |-> audiodata_32 == audiodata_32_p
    );

    // Data ready should be cleared after audio data is updated
    data_ready_clear: assert property (
        @(posedge clk) disable iff (!reset_n) data_rdy |-> !data_rdy
    );
endmodule