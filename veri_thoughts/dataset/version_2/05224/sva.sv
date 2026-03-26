module sel_Data_sva (
    input logic        CLK,
    input logic        RST,
    input logic [1:0]  SW,
    input logic [9:0]  xAxis,
    input logic [9:0]  yAxis,
    input logic [9:0]  zAxis,
    input logic [9:0]  DOUT,
    input logic [2:0]  LED
);

    // SW=00 selects xAxis directly when xAxis is non-negative.
    check_select_x_positive: assert property (
        @(posedge CLK) disable iff (RST)
        (SW == 2'b00 && xAxis[9] == 1'b0)
        |=> (LED == 3'b001 && DOUT == $past(xAxis))
    );

    // SW=00 selects xAxis sign-plus-magnitude when xAxis is negative.
    check_select_x_negative: assert property (
        @(posedge CLK) disable iff (RST)
        (SW == 2'b00 && xAxis[9] == 1'b1)
        |=> (LED == 3'b001 &&
             DOUT == {$past(xAxis[9]), (9'b000000000 - $past(xAxis[8:0]))})
    );

    // SW=01 selects yAxis directly when yAxis is non-negative.
    check_select_y_positive: assert property (
        @(posedge CLK) disable iff (RST)
        (SW == 2'b01 && yAxis[9] == 1'b0)
        |=> (LED == 3'b010 && DOUT == $past(yAxis))
    );

    // SW=01 selects yAxis sign-plus-magnitude when yAxis is negative.
    check_select_y_negative: assert property (
        @(posedge CLK) disable iff (RST)
        (SW == 2'b01 && yAxis[9] == 1'b1)
        |=> (LED == 3'b010 &&
             DOUT == {$past(yAxis[9]), (9'b000000000 - $past(yAxis[8:0]))})
    );

    // SW=10 selects zAxis directly when zAxis is non-negative.
    check_select_z_positive: assert property (
        @(posedge CLK) disable iff (RST)
        (SW == 2'b10 && zAxis[9] == 1'b0)
        |=> (LED == 3'b100 && DOUT == $past(zAxis))
    );

    // SW=10 selects zAxis sign-plus-magnitude when zAxis is negative.
    check_select_z_negative: assert property (
        @(posedge CLK) disable iff (RST)
        (SW == 2'b10 && zAxis[9] == 1'b1)
        |=> (LED == 3'b100 &&
             DOUT == {$past(zAxis[9]), (9'b000000000 - $past(zAxis[8:0]))})
    );

    // SW=11 takes the default path and selects xAxis directly when xAxis is non-negative.
    check_default_x_positive: assert property (
        @(posedge CLK) disable iff (RST)
        (SW == 2'b11 && xAxis[9] == 1'b0)
        |=> (LED == 3'b001 && DOUT == $past(xAxis))
    );

    // SW=11 takes the default path and selects xAxis sign-plus-magnitude when xAxis is negative.
    check_default_x_negative: assert property (
        @(posedge CLK) disable iff (RST)
        (SW == 2'b11 && xAxis[9] == 1'b1)
        |=> (LED == 3'b001 &&
             DOUT == {$past(xAxis[9]), (9'b000000000 - $past(xAxis[8:0]))})
    );

endmodule