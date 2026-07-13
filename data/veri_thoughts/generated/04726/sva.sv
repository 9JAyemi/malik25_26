module bw_clk_cclk_inv_48x_sva (
    input logic clkout,
    input logic clkin
);

    // Sampled on clkin rising edges, clkout stays the inverse of clkin.
    check_inversion_on_clkin_rise: assert property (
        @(posedge clkin) clkout == ~clkin
    );

    // Sampled on clkout rising edges, clkout stays the inverse of clkin.
    check_inversion_on_clkout_rise: assert property (
        @(posedge clkout) clkout == ~clkin
    );

endmodule