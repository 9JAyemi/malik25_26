
module rectangle_area(
    input [3:0] length,
    input [3:0] width,
    output reg [7:0] area
);

reg [3:0] length_reg;
reg [3:0] width_reg;

always @(*) begin
    length_reg = length;
    width_reg = width;
    area = length_reg * width_reg;
end

endmodule