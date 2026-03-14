module magnitude_comparator (
    input [3:0] a,
    input [3:0] b,
    output [1:0] out
);

    assign out = (a > b) ? 2'b01 : (a < b) ? 2'b10 : 2'b00;

endmodule