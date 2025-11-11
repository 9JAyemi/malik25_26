module shift_right #(parameter A_SIGNED = 0, A_WIDTH = 32, Y_WIDTH = 32) (
    input [A_WIDTH-1:0] A,
    input [4:0] B,
    output [A_WIDTH-1:0] Y
);

    wire [A_WIDTH-1:0] shifted;
    assign shifted = A >> B;

    assign Y = shifted;

endmodule