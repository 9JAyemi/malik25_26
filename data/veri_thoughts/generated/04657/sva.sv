module hw2_B_sva (
    input logic in,
    input logic clk,
    input logic rst_n,
    input logic out
);

    // When reset is sampled low, out must be low.
    check_reset_low_forces_out_low: assert property (
        @(posedge clk) disable iff ($initstate) !rst_n |-> (out == 1'b0)
    );

    // After a sampled reset-low cycle, out is still low before the next capture.
    check_post_reset_cycle_out_low: assert property (
        @(posedge clk) disable iff (!rst_n || $initstate) !$past(rst_n) |-> (out == 1'b0)
    );

    // A sampled 0 on in drives out low on the following active clock.
    check_low_input_captures_low: assert property (
        @(posedge clk) disable iff (!rst_n || $initstate) ($past(rst_n) && !$past(in)) |-> (out == 1'b0)
    );

    // A high out requires a sampled 1 on in in the prior active cycle.
    check_high_out_requires_prior_high_input: assert property (
        @(posedge clk) disable iff (!rst_n || $initstate) out |-> ($past(rst_n) && $past(in))
    );

endmodule