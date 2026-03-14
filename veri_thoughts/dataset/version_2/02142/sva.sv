module bw_clk_cclk_inv_64x_sva (
    input logic clkin,
    input logic clkout
);
    // Output equals bitwise inversion of input on clkin rising edge.
    check_inversion_pos: assert property (
        @(posedge clkin) clkout === ~clkin
    );
    // Output equals bitwise inversion of input on clkin falling edge.
    check_inversion_neg: assert property (
        @(negedge clkin) clkout === ~clkin
    );
    // A 0->1 transition on clkin causes a 1->0 transition on clkout.
    rise_in_fall_out: assert property (
        @(posedge clkin) $rose(clkin) |-> $fell(clkout)
    );
    // A 1->0 transition on clkin causes a 0->1 transition on clkout.
    fall_in_rise_out: assert property (
        @(negedge clkin) $fell(clkin) |-> $rose(clkout)
    );
    // At clkin rising edge, clkout must differ from clkin.
    not_equal_posedge: assert property (
        @(posedge clkin) clkout !== clkin
    );
    // At clkin falling edge, clkout must differ from clkin.
    not_equal_negedge: assert property (
        @(negedge clkin) clkout !== clkin
    );
endmodule