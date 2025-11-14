
module barrel_shifter (
    input clk,
    input [15:0] A,
    input [3:0] B,
    input S,
    output [15:0] P
);

reg [15:0] A_reg;
reg [3:0] B_reg;
reg S_reg;

always @(posedge clk) begin
    A_reg <= A;
    B_reg <= B;
    S_reg <= S;
end

wire [15:0] P_reg;

assign P_reg = S_reg ? {A_reg[15-B_reg+1:0], A_reg[15:15-B_reg+1]} : {A_reg[15:B_reg], 16'b0};

assign P = P_reg;

endmodule