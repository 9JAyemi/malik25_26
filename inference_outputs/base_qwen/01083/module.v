module adder(
    input [7:0] A,
    input [7:0] B,
    output [8:0] sum
);

    assign sum = {1'b0, A} + {1'b0, B};

endmodule

