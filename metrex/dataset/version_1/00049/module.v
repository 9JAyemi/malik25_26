
module priority_encoder (
    input [3:0] in,
    output reg [1:0] pos
);

wire [3:0] in_inv;
assign in_inv = ~in;

wire [1:0] sel;
assign sel = (in_inv[3:2] == 2'b00) ? 2'b00 :
             (in_inv[3:2] == 2'b01) ? 2'b01 :
             (in_inv[3:2] == 2'b10) ? 2'b10 :
             (in_inv[3:2] == 2'b11) ? 2'b11 : 2'b00;

always @(*) begin
    case (sel)
        2'b00: pos = 2'b00;
        2'b01: pos = 2'b01;
        2'b10: pos = 2'b10;
        2'b11: pos = 2'b11;
    endcase
end

endmodule
