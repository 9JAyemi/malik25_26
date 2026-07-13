module pwm_generator_sva (
    input logic clk,
    input logic rst_n,
    input logic pwm_out
);
    // During reset, pwm_out must be 0.
    reset_forces_low: assert property (
        @(posedge clk) !rst_n |-> (pwm_out == 1'b0)
    );

    // On each active clock, pwm_out toggles.
    toggle_each_cycle: assert property (
        @(posedge clk) disable iff (!rst_n) $past(rst_n) |-> (pwm_out == ~$past(pwm_out))
    );

    // If pwm_out is 0 at a clock edge, it must be 1 on the next clock.
    zero_implies_next_one: assert property (
        @(posedge clk) disable iff (!rst_n) (pwm_out == 1'b0) |=> (pwm_out == 1'b1)
    );

    // If pwm_out is 1 at a clock edge, it must be 0 on the next clock.
    one_implies_next_zero: assert property (
        @(posedge clk) disable iff (!rst_n) (pwm_out == 1'b1) |=> (pwm_out == 1'b0)
    );

    // Two consecutive active clocks return pwm_out to its value from two cycles earlier.
    two_cycle_periodicity: assert property (
        @(posedge clk) disable iff (!rst_n) $past(rst_n,2) |-> (pwm_out == $past(pwm_out,2))
    );

    // On reset deassertion, pwm_out is 0 at that clock edge.
    deassert_reset_low: assert property (
        @(posedge clk) $rose(rst_n) |-> (pwm_out == 1'b0)
    );

    // On reset deassertion, pwm_out is 1 on the next clock edge.
    deassert_reset_next_high: assert property (
        @(posedge clk) $rose(rst_n) |=> (pwm_out == 1'b1)
    );
endmodule