
module binary_to_gray (
    input [3:0] binary,
    output [3:0] gray
);

    // Intermediate signals
    wire [3:0] xor_out;
    wire [3:0] and_out;
    wire [3:0] not_out;

    // XOR gates
    xor (xor_out[1], binary[0], binary[1]);
    xor (xor_out[3], binary[2], binary[3]);
    xor (xor_out[2], xor_out[1], xor_out[3]);
    xor (xor_out[0], binary[1], binary[2]);

    // AND gates
    and (and_out[1], binary[0], binary[1]);
    and (and_out[3], binary[2], binary[3]);
    and (and_out[2], xor_out[1], xor_out[3]);
    and (and_out[0], binary[1], binary[2]);

    // NOT gates
    not (not_out[0], binary[0]);
    not (not_out[1], binary[1]);
    not (not_out[2], binary[2]);
    not (not_out[3], binary[3]);

    // Gray code output
    assign gray[0] = binary[0];
    assign gray[1] = xor_out[1];
    assign gray[2] = xor_out[2];
    assign gray[3] = xor_out[3];

endmodule
