
module binary_to_gray (
    input [8:0] binary,
    output [3:0] gray
);

    assign gray[3] = binary[8];
    assign gray[2] = binary[8] ^ binary[7];
    assign gray[1] = binary[7] ^ binary[6];
    assign gray[0] = binary[6] ^ binary[5];

endmodule
