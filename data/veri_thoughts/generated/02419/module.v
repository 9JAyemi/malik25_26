
module alt_priority_encoder(
    input [7:0] data,
    output reg [2:0] q
);

wire [3:0] ms_nibble;
wire [1:0] ls_nibble_enc;

// Extract most significant nibble
assign ms_nibble = data[7:4];

// Priority encoder for least significant nibble
priority_encoder_4bit ls_nibble_enc_inst(
    .data(data[3:0]),
    .q(ls_nibble_enc)
);

// Output logic
always @(*) begin
    case (ms_nibble)
        4'b0000: q = 3'b000;
        4'b1111: q = 3'b111;
        4'b1110: q = {1'b1, ls_nibble_enc};
        4'b1101: q = {1'b1, ls_nibble_enc + 2'b01};
        4'b1100: q = {1'b1, ls_nibble_enc + 2'b10};
        default: q = {1'b0, ls_nibble_enc};
    endcase
end

endmodule

module priority_encoder_4bit(
    input [3:0] data,
    output reg [1:0] q
);

always @(*) begin
    case (data)
        4'b0001: q = 2'b00;
        4'b0010: q = 2'b01;
        4'b0100: q = 2'b10;
        4'b1000: q = 2'b11;
        default: q = 2'b00;
    endcase
end

endmodule
