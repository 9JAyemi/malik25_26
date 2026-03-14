module bw_clk_cclk_inv_64x (
    clkout,
    clkin );

    output clkout;
    input  clkin;
 
    assign clkout = ~( clkin );

endmodule
