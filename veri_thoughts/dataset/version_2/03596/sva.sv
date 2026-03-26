module sel_Data_assertions (
    input logic        CLK,
    input logic        RST,
    input logic [1:0]  SW,
    input logic [9:0]  xAxis,
    input logic [9:0]  yAxis,
    input logic [9:0]  zAxis,
    input logic [9:0]  DOUT,
    input logic [2:0]  LED
);

    // A reset edge clears both registered outputs by the next sampled event.
    check_reset_clears_outputs: assert property (
        @(posedge CLK or posedge RST)
        $rose(RST) |=> ((LED == 3'b000) && (DOUT == 10'b0000000000))
    );

    // SW=00 selects xAxis directly when its sign bit is 0.
    check_sw00_x_nonnegative: assert property (
        @(posedge CLK or posedge RST) disable iff (RST)
        ((SW == 2'b00) && (xAxis[9] == 1'b0))
        |=> ((LED == 3'b001) && (DOUT == $past(xAxis)))
    );

    // SW=00 selects transformed xAxis when its sign bit is 1.
    check_sw00_x_negative: assert property (
        @(posedge CLK or posedge RST) disable iff (RST)
        ((SW == 2'b00) && (xAxis[9] == 1'b1))
        |=> ((LED == 3'b001) &&
             (DOUT[9] == 1'b1) &&
             (DOUT[8:0] == (9'b000000000 - $past(xAxis[8:0]))))
    );

    // SW=01 selects yAxis directly when its sign bit is 0.
    check_sw01_y_nonnegative: assert property (
        @(posedge CLK or posedge RST) disable iff (RST)
        ((SW == 2'b01) && (yAxis[9] == 1'b0))
        |=> ((LED == 3'b010) && (DOUT == $past(yAxis)))
    );

    // SW=01 selects transformed yAxis when its sign bit is 1.
    check_sw01_y_negative: assert property (
        @(posedge CLK or posedge RST) disable iff (RST)
        ((SW == 2'b01) && (yAxis[9] == 1'b1))
        |=> ((LED == 3'b010) &&
             (DOUT[9] == 1'b1) &&
             (DOUT[8:0] == (9'b000000000 - $past(yAxis[8:0]))))
    );

    // SW=10 selects zAxis directly when its sign bit is 0.
    check_sw10_z_nonnegative: assert property (
        @(posedge CLK or posedge RST) disable iff (RST)
        ((SW == 2'b10) && (zAxis[9] == 1'b0))
        |=> ((LED == 3'b100) && (DOUT == $past(zAxis)))
    );

    // SW=10 selects transformed zAxis when its sign bit is 1.
    check_sw10_z_negative: assert property (
        @(posedge CLK or posedge RST) disable iff (RST)
        ((SW == 2'b10) && (zAxis[9] == 1'b1))
        |=> ((LED == 3'b100) &&
             (DOUT[9] == 1'b1) &&
             (DOUT[8:0] == (9'b000000000 - $past(zAxis[8:0]))))
    );

    // SW=11 follows the default branch and selects xAxis directly when its sign bit is 0.
    check_sw11_default_x_nonnegative: assert property (
        @(posedge CLK or posedge RST) disable iff (RST)
        ((SW == 2'b11) && (xAxis[9] == 1'b0))
        |=> ((LED == 3'b001) && (DOUT == $past(xAxis)))
    );

    // SW=11 follows the default branch and selects transformed xAxis when its sign bit is 1.
    check_sw11_default_x_negative: assert property (
        @(posedge CLK or posedge RST) disable iff (RST)
        ((SW == 2'b11) && (xAxis[9] == 1'b1))
        |=> ((LED == 3'b001) &&
             (DOUT[9] == 1'b1) &&
             (DOUT[8:0] == (9'b000000000 - $past(xAxis[8:0]))))
    );

endmodule