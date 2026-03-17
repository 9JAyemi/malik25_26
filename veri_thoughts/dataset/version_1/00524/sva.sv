module pwm_generator_sva (
    input logic clk,
    input logic rst_n,
    input logic pwm_out
);

    // A sampled active-low reset keeps the output low at the next clock sample.
    check_reset_forces_low_next_sample: assert property (
        @(posedge clk) !rst_n |=> (pwm_out == 1'b0)
    );

    // The first sampled cycle after a sampled reset low still sees the output low.
    check_release_from_reset_starts_low: assert property (
        @(posedge clk) (($past(rst_n) === 1'b0) && (rst_n == 1'b1)) |-> (pwm_out == 1'b0)
    );

    // A sampled high output must be low on the next clock sample.
    check_high_sample_falls_next_cycle: assert property (
        @(posedge clk) (pwm_out == 1'b1) |=> (pwm_out == 1'b0)
    );

    // Any sampled high output must come from a previous low sample out of reset.
    check_high_sample_comes_from_prev_low: assert property (
        @(posedge clk) disable iff (!rst_n)
        (((($past(rst_n) === 1'b0) || ($past(rst_n) === 1'b1))) && (pwm_out == 1'b1))
        |-> (($past(rst_n) === 1'b1) && ($past(pwm_out) === 1'b0))
    );

endmodule