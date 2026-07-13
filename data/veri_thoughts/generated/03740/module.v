module mux2to1 (
    input wire [31:0] A,
    input wire [31:0] B,
    input wire S,
    output wire [31:0] Y
);

    assign Y = (S == 0) ? A : B;

endmodule