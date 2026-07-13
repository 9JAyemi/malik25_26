module bw_clk_gclk_inv_r90_192x_sva (
    input logic clkout,
    input logic clkin
);

    // On a clkin rise, the sampled low-input state must have clkout high.
    check_clkout_high_before_clkin_rise: assert property (
        @(posedge clkin) clkout === 1'b1
    );

    // On a clkin fall, the sampled high-input state must have clkout low.
    check_clkout_low_before_clkin_fall: assert property (
        @(negedge clkin) clkout === 1'b0
    );

endmodule