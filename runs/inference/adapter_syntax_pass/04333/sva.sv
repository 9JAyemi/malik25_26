module bw_clk_gclk_inv_r90_192x_sva (
    input logic clkout,
    input logic clkin
);

    // clkout must always be the logical inverse of clkin.
    check_clkout_is_inverted_clkin: assert property (
        @($global_clock) clkout === ~clkin
    );

endmodule