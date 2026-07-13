module decoder (
    input [3:0] in,
    output [15:0] out
);

    assign out = 16'b0000000000000001 << in;

endmodule