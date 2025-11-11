
module converter(
    input [3:0] in,
    output [3:0] out
);

reg [3:0] out_reg;

always @* begin
    case (in)
        4'b0000: out_reg = 4'b0000;
        4'b0001, 4'b0010: out_reg = 4'b0001;
        4'b0011, 4'b0100: out_reg = 4'b0010;
        4'b0101, 4'b0110: out_reg = 4'b0011;
        4'b0111, 4'b1000: out_reg = 4'b0100;
        4'b1001, 4'b1010: out_reg = 4'b0101;
        4'b1011, 4'b1100: out_reg = 4'b0110;
        4'b1101, 4'b1110: out_reg = 4'b0111;
        4'b1111: out_reg = 4'b1000;
    endcase
end

assign out = out_reg;

endmodule
