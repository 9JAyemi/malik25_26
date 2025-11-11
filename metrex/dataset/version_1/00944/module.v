
module binary_to_excess3 (
    input [3:0] B,
    output [3:0] E3
);

assign E3 = B + 3;

endmodule
module top_module (
    input [7:0] A,
    input [7:0] B,
    output [7:0] E
);

wire [7:0] sum;
binary_to_excess3 b2e1(.B(sum[3:0]), .E3(E[3:0]));
binary_to_excess3 b2e2(.B(sum[7:4]), .E3(E[7:4]));

assign sum = A + B;

endmodule