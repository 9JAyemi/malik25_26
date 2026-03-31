module pwm_generator_sva (
    input logic clk,
    input logic rst_n,
    input logic pwm_out
);

    // Active-low reset forces pwm_out low.
    check_reset_forces_low: assert property (
        @(posedge clk) !rst_n |-> (pwm_out == 1'b0)
    );

    // A sampled reset cycle leaves pwm_out low on the next clock.
    check_reset_holds_low_next_cycle: assert property (
        @(posedge clk) !rst_n |=> (pwm_out == 1'b0)
    );

    // Outside reset, pwm_out is high on the first active clock after reset release.
    check_release_starts_high: assert property (
        @(posedge clk) disable iff (!rst_n) $rose(rst_n) |-> (pwm_out == 1'b1)
    );

    // Outside reset, pwm_out toggles every active clock.
    check_toggle_every_active_cycle: assert property (
        @(posedge clk) disable iff (!rst_n) 1'b1 |=> (pwm_out == ~$past(pwm_out))
    );

endmodule