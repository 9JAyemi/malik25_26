module decoder_4to16_pipeline (
    input [1:0] select,
    input en,
    input clk,
    output reg [15:0] out
);

reg [1:0] select_reg;
reg en_reg;

always @(posedge clk) begin
    select_reg <= select;
    en_reg <= en;
end

always @(posedge clk) begin
    if (en_reg == 0) begin
        case (select_reg)
            2'b00: out <= 16'b1111111111111110;
            2'b01: out <= 16'b1111111111111101;
            2'b10: out <= 16'b1111111111111011;
            2'b11: out <= 16'b1111111111110111;
        endcase;
    end else begin
        out <= 16'b1111111111111111;
    end
end

endmodule