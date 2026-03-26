module bw_clk_gclk_inv_r90_256x_sva (
    input logic clkout,
    input logic clkin
);

    // Sampled input and output are complementary on clkin rising edges.
    check_inv_relation_on_clkin_rise: assert property (
        @(posedge clkin) clkout === ~clkin
    );

    // Sampled input and output are complementary on clkin falling edges.
    check_inv_relation_on_clkin_fall: assert property (
        @(negedge clkin) clkout === ~clkin
    );

    // Sampled input and output are complementary on clkout rising edges.
    check_inv_relation_on_clkout_rise: assert property (
        @(posedge clkout) clkout === ~clkin
    );

    // Sampled input and output are complementary on clkout falling edges.
    check_inv_relation_on_clkout_fall: assert property (
        @(negedge clkout) clkout === ~clkin
    );

endmodule