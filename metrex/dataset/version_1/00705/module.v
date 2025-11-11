module bitwise_and #(
    parameter bits = 16
) (
    input [bits-1:0] a, b,
    output [bits-1:0] q
);
    assign q = a & b;
endmodule