module register_sva (
    input logic clk,
    input logic reset,
    input logic xclear,
    input logic xload,
    input logic [WIDTH-1:0] xin,
    output logic [WIDTH-1:0] xout
);
    parameter WIDTH = 8;

    ///// Register behavior /////
    // Register output is zero when either xclear or reset is asserted.
    clear_or_reset: assert property (
        @(posedge clk) disable iff (!reset) (xclear || reset) |-> (xout == 0)
    );

    // Register output is loaded with xin when xload is asserted and neither xclear nor reset is asserted.
    load: assert property (
        @(posedge clk) disable iff (!reset) (xload && !xclear && !reset) |-> (xout == xin)
    );

    // Register output remains unchanged when neither xload, xclear, nor reset is asserted.
    no_change: assert property (
        @(posedge clk) disable iff (!reset) (!xload && !xclear && !reset) |-> (xout == xout)
    );
endmodule