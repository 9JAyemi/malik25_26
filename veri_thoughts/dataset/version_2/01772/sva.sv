module bw_clk_gclk_inv_r90_224x_sva (
    input logic clkout,
    input logic clkin
);
    // On clkin rising edge, clkout equals bitwise inversion of clkin.
    check_inversion_on_posedge: assert property (
        @(posedge clkin) clkout === ~clkin
    );

    // On clkin falling edge, clkout equals bitwise inversion of clkin.
    check_inversion_on_negedge: assert property (
        @(negedge clkin) clkout === ~clkin
    );

    // If previous clkin was 0, a rising clkin causes clkout to fall.
    check_out_falls_on_in_rise: assert property (
        @(posedge clkin) ($past(clkin) === 1'b0) |-> $fell(clkout)
    );

    // If previous clkin was 1, a falling clkin causes clkout to rise.
    check_out_rises_on_in_fall: assert property (
        @(negedge clkin) ($past(clkin) === 1'b1) |-> $rose(clkout)
    );
endmodule