
module ripple_carry_adder (
    input [3:0] A,
    input [3:0] B,
    input CIN,
    output [3:0] SUM,
    output COUT
);

reg [3:0] A_reg, B_reg;
wire [3:0] SUM1, SUM2, SUM3; 
wire COUT1, COUT2, COUT3;
reg CIN_reg;

full_adder FA1(A_reg[0], B_reg[0], CIN_reg, SUM1[0], COUT1);
full_adder FA2(A_reg[1], B_reg[1], COUT1, SUM2[1], COUT2);
full_adder FA3(A_reg[2], B_reg[2], COUT2, SUM3[2], COUT3);
full_adder FA4(A_reg[3], B_reg[3], COUT3, SUM[3], COUT);

assign SUM[2] = SUM3[2];
assign SUM[1] = SUM2[1];
assign SUM[0] = SUM1[0];

always @(A or B or CIN) begin
    A_reg <= A;
    B_reg <= B;
    CIN_reg <= CIN;
end

endmodule
module full_adder (
    input A,
    input B,
    input CIN,
    output SUM,
    output COUT
);

assign {COUT, SUM} = A + B + CIN;

endmodule