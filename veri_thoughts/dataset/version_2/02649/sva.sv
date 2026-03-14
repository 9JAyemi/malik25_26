module servo_sva #(
    parameter WIDTH = 16,
    parameter NUM   = 1
) (
    input  logic                     clk50Mhz,
    input  logic                     rst,
    input  logic [(WIDTH*NUM)-1:0]   posArray,
    input  logic [NUM-1:0]           pwm,
    input  logic [19:0]              counter
);

    // Counter must be 0 when synchronous reset is asserted.
    check_reset_counter_zero: assert property (
        @(posedge clk50Mhz) disable iff (1'b0) rst |-> (counter == 20'd0)
    );

    // PWM outputs must be 0 when synchronous reset is asserted.
    check_reset_pwm_zero: assert property (
        @(posedge clk50Mhz) disable iff (1'b0) rst |-> (pwm == {NUM{1'b0}})
    );

    // On the first cycle after reset deasserts, counter increments from 0 to 1.
    check_counter_after_reset: assert property (
        @(posedge clk50Mhz) disable iff (rst) $fell(rst) |-> (counter == 20'd1)
    );

    // Counter increments by 1 every cycle when not in reset (mod 2^20).
    check_counter_increments: assert property (
        @(posedge clk50Mhz) disable iff (rst) counter == ($past(counter) + 20'd1)
    );

    // When previous counter was max, it wraps to 0 on the next cycle.
    check_counter_wrap: assert property (
        @(posedge clk50Mhz) disable iff (rst) ($past(counter) == 20'hFFFFF) |-> (counter == 20'd0)
    );

    genvar i;
    generate
        for (i = 0; i < NUM; i = i + 1) begin : per_channel_checks
            // PWM[i] equals comparator result computed with previous counter value.
            check_pwm_functional_i: assert property (
                @(posedge clk50Mhz) disable iff (rst)
                    pwm[i] ==
                    ( ( (posArray[(WIDTH*(i+1)-1):(WIDTH*i)] << (16-WIDTH)) + 16'd42232 ) > $past(counter) )
            );

            // If comparator is true with previous counter, PWM[i] must be 1 this cycle.
            check_pwm_high_condition_i: assert property (
                @(posedge clk50Mhz) disable iff (rst)
                    ( ( (posArray[(WIDTH*(i+1)-1):(WIDTH*i)] << (16-WIDTH)) + 16'd42232 ) > $past(counter) )
                    |-> pwm[i] == 1'b1
            );

            // If comparator is false with previous counter, PWM[i] must be 0 this cycle.
            check_pwm_low_condition_i: assert property (
                @(posedge clk50Mhz) disable iff (rst)
                    ! ( ( (posArray[(WIDTH*(i+1)-1):(WIDTH*i)] << (16-WIDTH)) + 16'd42232 ) > $past(counter) )
                    |-> pwm[i] == 1'b0
            );

            // On the first non-reset cycle, PWM[i] must be 1 (threshold > 0 always holds).
            check_pwm_after_reset_deassert_i: assert property (
                @(posedge clk50Mhz) disable iff (rst) $fell(rst) |-> (pwm[i] == 1'b1)
            );
        end
    endgenerate

endmodule