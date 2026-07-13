
module barrel_shifter (
    input [3:0] DATA,
    input [1:0] SHIFT,
    output [3:0] OUT
);

    assign OUT[3] = SHIFT[1] ? DATA[1] : SHIFT[0] ? DATA[2] : SHIFT[0] ? DATA[2] : SHIFT[1] ? DATA[2] : SHIFT[1] ? DATA[0] : 1'b0;
    assign OUT[2] = SHIFT[1] ? DATA[0] : SHIFT[0] ? DATA[3] : SHIFT[0] ? DATA[3] : SHIFT[1] ? DATA[1] : SHIFT[1] ? DATA[3] : 1'b0;
    assign OUT[1] = SHIFT[1] ? DATA[3] : SHIFT[0] ? DATA[2] : SHIFT[0] ? DATA[2] : SHIFT[1] ? DATA[0] : SHIFT[1] ? DATA[1] : 1'b0;
    assign OUT[0] = SHIFT[1] ? DATA[2] : SHIFT[0] ? DATA[1] : SHIFT[0] ? DATA[1] : SHIFT[1] ? DATA[3] : SHIFT[1] ? DATA[2] : 1'b0;

endmodule