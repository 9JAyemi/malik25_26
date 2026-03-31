module bw_clk_gclk_inv_r90_192x_sva (
    input logic clkout,
    input logic clkin
);

// clkout is always the bitwise inversion of clkin.
    check_inversion_exact: assert property (
        @(posedge clkin) clkout == ~clkin
    );

// A high clkin must produce a low clkout.
    check_clkin_high_drives_clkout_low: assert property (
        @(posedge clkin) clkin |-> !clkout
    );

// A low clkin must produce a high clkout.
    check_clkin_low_drives_clkout_high: assert property (
        @(posedge clkin) !clkin |-> clkout
    );

endmodule
