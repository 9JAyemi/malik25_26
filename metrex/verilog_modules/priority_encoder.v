
module priority_encoder (
    input [7:0] in,
    output wire [2:0] pos );

    wire [7:0] and_out;
    wire [2:0] gray_out;

    assign and_out = {in[7] & in[6], in[6] & ~in[7], in[5] & ~in[7] & ~in[6], in[4] & ~in[7] & ~in[6] & ~in[5], in[3] & ~in[7] & ~in[6] & ~in[5] & ~in[4], in[2] & ~in[7] & ~in[6] & ~in[5] & ~in[4] & ~in[3], in[1] & ~in[7] & ~in[6] & ~in[5] & ~in[4] & ~in[3] & ~in[2], in[0] & ~in[7] & ~in[6] & ~in[5] & ~in[4] & ~in[3] & ~in[2] & ~in[1]};

    gray_to_binary gray_converter(
        .gray(gray_out),
        .binary(pos)
    );

    assign gray_out = {and_out[7], and_out[6] ^ and_out[7], and_out[5] ^ and_out[6], and_out[4] ^ and_out[5], and_out[3] ^ and_out[4], and_out[2] ^ and_out[3], and_out[1] ^ and_out[2], and_out[0] ^ and_out[1]};

endmodule

module gray_to_binary (
    input [2:0] gray,
    output reg [2:0] binary );

    always @* begin
        case (gray)
            3'b000: binary = 3'b000;
            3'b001: binary = 3'b001;
            3'b010: binary = 3'b011;
            3'b011: binary = 3'b010;
            3'b100: binary = 3'b110;
            3'b101: binary = 3'b111;
            3'b110: binary = 3'b101;
            3'b111: binary = 3'b100;
        endcase
    end

endmodule
