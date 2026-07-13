module binary_decoder_3to8 (
    input [2:0] in,      // 3-bit input
    output reg [7:0] out // 8-bit output
);

    always @(*) begin
        // Initialize output to 0
        out = 8'b00000000;

        // Decode the input to one-hot output
        case (in)
            3'b000: out[0] = 1'b1;
            3'b001: out[1] = 1'b1;
            3'b010: out[2] = 1'b1;
            3'b011: out[3] = 1'b1;
            3'b100: out[4] = 1'b1;
            3'b101: out[5] = 1'b1;
            3'b110: out[6] = 1'b1;
            3'b111: out[7] = 1'b1;
            default: out = 8'b00000000; // Default case to handle unknown states
        endcase
    end

endmodule
