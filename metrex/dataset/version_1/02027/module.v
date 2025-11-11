module mouse_painter(
    input [4:0] line_number,
    output reg [7:0] line_code
);

parameter [7:0] line00 = 8'h01;
parameter [7:0] line01 = 8'h03;
parameter [7:0] line02 = 8'h07;
parameter [7:0] line03 = 8'h0F;
parameter [7:0] line04 = 8'h1F;
parameter [7:0] line05 = 8'h3F;
parameter [7:0] line06 = 8'h7F;
parameter [7:0] line07 = 8'hFF;
parameter [7:0] line08 = 8'h07;
parameter [7:0] line09 = 8'h03;
parameter [7:0] line10 = 8'h01;

always @(*) begin
    case(line_number)
        5'b00000 : line_code = line00;
        5'b00001 : line_code = line01;
        5'b00010 : line_code = line02;
        5'b00011 : line_code = line03;
        5'b00100 : line_code = line04;
        5'b00101 : line_code = line05;
        5'b00110 : line_code = line06;
        5'b00111 : line_code = line07;
        5'b01000 : line_code = line08;
        5'b01001 : line_code = line09;
        5'b01010 : line_code = line10;
        default : line_code = 8'b00000000;
    endcase
end

endmodule