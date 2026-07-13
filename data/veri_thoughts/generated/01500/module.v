module decoder_2to4 (
    input [1:0] in,
    input clk,
    output reg [3:0] out
);

reg [3:0] out_reg;

always @(*) begin
    case(in)
        2'b00: out_reg = 4'b0001;
        2'b01: out_reg = 4'b0010;
        2'b10: out_reg = 4'b0100;
        2'b11: out_reg = 4'b1000;
    endcase;
end

always @(posedge clk) begin
    out <= out_reg;
end

endmodule