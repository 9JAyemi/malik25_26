module binary_to_bcd (
    input [3:0] binary_in,
    output [7:0] bcd_out,
    output overflow
);

    wire [3:0] digit;
    wire [3:0] carry;
    wire [7:0] bcd;

    assign digit[0] = binary_in[0];
    assign digit[1] = binary_in[1];
    assign digit[2] = binary_in[2];
    assign digit[3] = binary_in[3];

    assign bcd[0] = digit[0] + digit[1]*2 + digit[2]*4 + digit[3]*8;
    assign bcd[1] = digit[0]*2 + digit[1]*4 + digit[2]*8;
    assign bcd[2] = digit[0]*4 + digit[1]*8;
    assign bcd[3] = digit[0]*8;

    assign carry[0] = (bcd[0] > 9);
    assign carry[1] = (bcd[1] > 9);
    assign carry[2] = (bcd[2] > 9);
    assign carry[3] = (bcd[3] > 9);

    assign bcd_out[0] = bcd[0];
    assign bcd_out[1] = bcd[1];
    assign bcd_out[2] = bcd[2];
    assign bcd_out[3] = bcd[3];
    assign bcd_out[4] = carry[0];
    assign bcd_out[5] = carry[1];
    assign bcd_out[6] = carry[2];
    assign bcd_out[7] = carry[3];

    assign overflow = (carry[3] == 1);

endmodule

module binary_to_excess3 (
    input [3:0] binary_in,
    output [3:0] excess3_out
);

    assign excess3_out[0] = binary_in[0] ^ 1 ^ 1 ^ 1;
    assign excess3_out[1] = binary_in[1] ^ 1 ^ 1 ^ 1;
    assign excess3_out[2] = binary_in[2] ^ 1 ^ 1 ^ 1;
    assign excess3_out[3] = binary_in[3] ^ 1 ^ 1 ^ 1;

endmodule

module top_module (
    input [3:0] B,
    output [7:0] bcd_out,
    output overflow,
    output reg [3:0] E,
    output reg [3:0] sum
);

    wire [3:0] binary_out;
    wire [3:0] excess3_out;

    binary_to_excess3 bin2ex3(.binary_in(B), .excess3_out(excess3_out));
    binary_to_bcd bin2bcd(.binary_in(excess3_out), .bcd_out(bcd_out), .overflow(overflow));

    always @* begin
        E = excess3_out;
        sum = B + E;
    end

endmodule