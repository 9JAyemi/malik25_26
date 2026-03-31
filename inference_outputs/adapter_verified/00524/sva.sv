module pwm_generator_sva (
    input logic clk,
    input logic rst_n,
    input logic pwm_out
);

// Clock: clk (posedge). Reset: rst_n active-low, asynchronous.
    // Logic: sequential toggle on clk; output is 0 when reset is asserted.

    // During reset, pwm_out must be 0.
    check_reset_forces_low: assert property (
        @(posedge clk) !rst_n |-> (pwm_out == 1'b0)
    );

// On the first clock after reset deasserts, pwm_out is still 0.
    check_first_cycle_after_reset_release: assert property (
        @(posedge clk) disable iff (!rst_n) $rose(rst_n) |-> (pwm_out == 1'b0)
    );

// On the second clock after reset deasserts, pwm_out is 1.
    check_second_cycle_after_reset_release: assert property (
        @(posedge clk) disable iff (!rst_n) $rose(rst_n) |-> ##1 (pwm_out == 1'b1)
    );

// After reset deasserts, pwm_out toggles every clock.
    check_toggle_every_cycle: assert property (
        @(posedge clk) disable iff (!rst_n) $rose(rst_n) |-> ##1 (pwm_out == ~$past(pwm_out))
    );

endmodule
