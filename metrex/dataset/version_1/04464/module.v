
module gray_code_converter (
    input [3:0] data_in,
    output [3:0] gray_out
);

    wire [3:0] intermediate;

    assign intermediate[0] = data_in[0];
    assign intermediate[1] = data_in[0] ^ data_in[1];
    assign intermediate[2] = data_in[1] ^ data_in[2];
    assign intermediate[3] = data_in[2] ^ data_in[3];

    assign gray_out = intermediate;

endmodule
