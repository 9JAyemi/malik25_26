
module max_value (
    input [4:0] a,
    input [4:0] b,
    output [4:0] result
);

    assign result = (a >= b) ? a : b;

endmodule