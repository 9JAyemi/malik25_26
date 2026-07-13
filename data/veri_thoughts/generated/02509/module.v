
module priority_encoder (
    input [3:0] in,
    output [1:0] pos
);

reg [1:0] pos_reg;

always @ (in) begin
    case (in)
        4'b1000: pos_reg = 3;
        4'b0100: pos_reg = 2;
        4'b0010: pos_reg = 1;
        4'b0001: pos_reg = 0;
        default: pos_reg = 2'b0;
    endcase
end

assign pos = pos_reg;

endmodule

module top_module (
    input [3:0] in,
    output [1:0] pos
);

priority_encoder pe(.in(in), .pos(pos));

endmodule
