module exercise_8_10_sva (
    input  logic [1:0] state,
    input  logic       x,
    input  logic       y,
    input  logic       Clk
);
    // XY=00, state=00 -> next 00
    check_xy00_s00_to_00: assert property (
        @(posedge Clk) ({x,y} == 2'b00 && state == 2'b00) |=> (state == 2'b00)
    );
    // XY=00, state=01 -> next 10
    check_xy00_s01_to_10: assert property (
        @(posedge Clk) ({x,y} == 2'b00 && state == 2'b01) |=> (state == 2'b10)
    );
    // XY=00, state=10 -> next 00
    check_xy00_s10_to_00: assert property (
        @(posedge Clk) ({x,y} == 2'b00 && state == 2'b10) |=> (state == 2'b00)
    );
    // XY=00, state=11 -> next 10
    check_xy00_s11_to_10: assert property (
        @(posedge Clk) ({x,y} == 2'b00 && state == 2'b11) |=> (state == 2'b10)
    );

    // XY=01, state=00 -> next 00
    check_xy01_s00_to_00: assert property (
        @(posedge Clk) ({x,y} == 2'b01 && state == 2'b00) |=> (state == 2'b00)
    );
    // XY=01, state=01 -> next 11
    check_xy01_s01_to_11: assert property (
        @(posedge Clk) ({x,y} == 2'b01 && state == 2'b01) |=> (state == 2'b11)
    );
    // XY=01, state=10 -> next 00
    check_xy01_s10_to_00: assert property (
        @(posedge Clk) ({x,y} == 2'b01 && state == 2'b10) |=> (state == 2'b00)
    );
    // XY=01, state=11 -> next 11
    check_xy01_s11_to_11: assert property (
        @(posedge Clk) ({x,y} == 2'b01 && state == 2'b11) |=> (state == 2'b11)
    );

    // XY=10, state=00 -> next 01
    check_xy10_s00_to_01: assert property (
        @(posedge Clk) ({x,y} == 2'b10 && state == 2'b00) |=> (state == 2'b01)
    );
    // XY=10, state=01 -> next 10
    check_xy10_s01_to_10: assert property (
        @(posedge Clk) ({x,y} == 2'b10 && state == 2'b01) |=> (state == 2'b10)
    );
    // XY=10, state=10 -> next 10
    check_xy10_s10_to_10: assert property (
        @(posedge Clk) ({x,y} == 2'b10 && state == 2'b10) |=> (state == 2'b10)
    );
    // XY=10, state=11 -> next 00
    check_xy10_s11_to_00: assert property (
        @(posedge Clk) ({x,y} == 2'b10 && state == 2'b11) |=> (state == 2'b00)
    );

    // XY=11, state=00 -> next 01
    check_xy11_s00_to_01: assert property (
        @(posedge Clk) ({x,y} == 2'b11 && state == 2'b00) |=> (state == 2'b01)
    );
    // XY=11, state=01 -> next 11
    check_xy11_s01_to_11: assert property (
        @(posedge Clk) ({x,y} == 2'b11 && state == 2'b01) |=> (state == 2'b11)
    );
    // XY=11, state=10 -> next 11
    check_xy11_s10_to_11: assert property (
        @(posedge Clk) ({x,y} == 2'b11 && state == 2'b10) |=> (state == 2'b11)
    );
    // XY=11, state=11 -> next 00
    check_xy11_s11_to_00: assert property (
        @(posedge Clk) ({x,y} == 2'b11 && state == 2'b11) |=> (state == 2'b00)
    );
endmodule