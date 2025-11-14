module _90_pmux2 (A, B, S, Y);
	parameter WIDTH = 1;
	parameter S_WIDTH = 1;

	input [WIDTH-1:0] A;
	input [WIDTH*S_WIDTH-1:0] B;
	input [S_WIDTH-1:0] S;
	output [WIDTH-1:0] Y;

	wire [S_WIDTH-1:0] S_NOT;
	wire [WIDTH*S_WIDTH-1:0] B_NOT;

	assign S_NOT = ~S;
	assign B_NOT = ~B;

	wire [WIDTH-1:0] A_AND_S_NOT;
	wire [WIDTH*S_WIDTH-1:0] B_AND_S;

	assign A_AND_S_NOT = A & {WIDTH{S_NOT}};
	assign B_AND_S = B & {WIDTH*S_WIDTH{S_NOT}};

	wire [WIDTH-1:0] Y_B_AND_S_NOT;
	wire [S_WIDTH-1:0] Y_B_AND_S_NOT_OR;

	assign Y_B_AND_S_NOT = |B_AND_S;
	assign Y_B_AND_S_NOT_OR = |{S_WIDTH{Y_B_AND_S_NOT}};

	assign Y = S ? Y_B_AND_S_NOT_OR : A_AND_S_NOT;
endmodule