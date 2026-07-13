module adder_module (
    input signed [31:0] A,
    input signed [31:0] B,
    output signed [31:0] Y
);

    assign Y = A + B;

endmodule