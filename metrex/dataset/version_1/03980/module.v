module comparator (
    input [3:0] A,
    input [3:0] B,
    input clk,
    output reg [1:0] OUT
);

reg [3:0] A_reg, B_reg;
reg [1:0] OUT_reg;

always @ (posedge clk) begin
    A_reg <= A;
    B_reg <= B;

    if (A_reg > B_reg) begin
        OUT_reg <= 2'b01;
    end else if (A_reg < B_reg) begin
        OUT_reg <= 2'b10;
    end else begin
        OUT_reg <= 2'b11;
    end
end

always @*
    OUT = OUT_reg;

endmodule