module c_clkgate_sva (
    input logic clk,
    input logic active,
    input logic clk_gated
);

    // clk_gated must equal clk AND the prior-cycle active sample.
    check_clk_gated_definition: assert property (
        @(posedge clk) 1'b1 |=> (clk_gated == (clk & $past(active)))
    );

    // A low clk must force clk_gated low.
    check_clk_low_forces_clk_gated_low: assert property (
        @(posedge clk) (clk == 1'b0) |=> (clk_gated == 1'b0)
    );

    // A high clk with a high prior-cycle active sample must drive clk_gated high.
    check_active_sample_high_drives_clk_gated_high: assert property (
        @(posedge clk) ((clk == 1'b1) && ($past(active) == 1'b1)) |=> (clk_gated == 1'b1)
    );

    // A high clk with a low prior-cycle active sample must drive clk_gated low.
    check_active_sample_low_drives_clk_gated_low: assert property (
        @(posedge clk) ((clk == 1'b1) && ($past(active) == 1'b0)) |=> (clk_gated == 1'b0)
    );

endmodule