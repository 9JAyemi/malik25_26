
module sub (
    // Outputs
    outy_w92, outz_w22,
    // Inputs
    clk, inw_w31, inx_w11
    );

    input clk;
    input        inw_w31;
    input [60:0] inx_w11;
    output [91:0] outy_w92;
    output [21:0] outz_w22;

    wire [29:0] outc_w30;
    wire [72:0] outd_w73;
endmodule

module t (
    // Outputs
    outc_w30,
    outd_w73,
    // Inputs
    clk,
    ina_w1,
    inb_w61
    );

    input clk;
    input ina_w1;
    input [60:0] inb_w61;
    output [29:0] outc_w30;
    output [72:0] outd_w73;

    assign outc_w30 = ina_w1 - inb_w61[30:0];
    assign outd_w73 = ina_w1 * inb_w61;

endmodule
