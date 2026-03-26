module exercise_8_10_assertions (
    input logic [1:0] state,
    input logic x,
    input logic y,
    input logic Clk
);

    // From state 00, x=0 keeps the state at 00.
    check_state_00_x0_hold: assert property (
        @(posedge Clk) (state == 2'b00 && x == 1'b0) |=> (state == 2'b00)
    );

    // From state 00, x=1 moves the state to 01.
    check_state_00_x1_to_01: assert property (
        @(posedge Clk) (state == 2'b00 && x == 1'b1) |=> (state == 2'b01)
    );

    // From state 01, y=0 moves the state to 10.
    check_state_01_y0_to_10: assert property (
        @(posedge Clk) (state == 2'b01 && y == 1'b0) |=> (state == 2'b10)
    );

    // From state 01, y=1 moves the state to 11.
    check_state_01_y1_to_11: assert property (
        @(posedge Clk) (state == 2'b01 && y == 1'b1) |=> (state == 2'b11)
    );

    // From state 10, x=0 moves the state to 00.
    check_state_10_x0_to_00: assert property (
        @(posedge Clk) (state == 2'b10 && x == 1'b0) |=> (state == 2'b00)
    );

    // From state 10 with x,y=10, the state holds at 10.
    check_state_10_xy10_hold: assert property (
        @(posedge Clk) (state == 2'b10 && x == 1'b1 && y == 1'b0) |=> (state == 2'b10)
    );

    // From state 10 with x,y=11, the state moves to 11.
    check_state_10_xy11_to_11: assert property (
        @(posedge Clk) (state == 2'b10 && x == 1'b1 && y == 1'b1) |=> (state == 2'b11)
    );

    // From state 11 with x,y=00, the state moves to 10.
    check_state_11_xy00_to_10: assert property (
        @(posedge Clk) (state == 2'b11 && x == 1'b0 && y == 1'b0) |=> (state == 2'b10)
    );

    // From state 11 with x,y=01, the state holds at 11.
    check_state_11_xy01_hold: assert property (
        @(posedge Clk) (state == 2'b11 && x == 1'b0 && y == 1'b1) |=> (state == 2'b11)
    );

    // From state 11, x=1 moves the state to 00.
    check_state_11_x1_to_00: assert property (
        @(posedge Clk) (state == 2'b11 && x == 1'b1) |=> (state == 2'b00)
    );

endmodule