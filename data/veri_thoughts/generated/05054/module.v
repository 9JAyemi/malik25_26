module PPgen(
	Single,
	Yi,
	Double,
	Negate,
	Yi_m1,
	PPi
);


input wire	Single;
input wire	Yi;
input wire	Double;
input wire	Negate;
input wire	Yi_m1;
output wire	PPi;

wire	SYNTHESIZED_WIRE_0;
wire	SYNTHESIZED_WIRE_1;
wire	SYNTHESIZED_WIRE_2;




assign	SYNTHESIZED_WIRE_1 = ~(Yi & Single);

assign	SYNTHESIZED_WIRE_0 = ~(Yi_m1 & Double);

assign	SYNTHESIZED_WIRE_2 = ~(SYNTHESIZED_WIRE_0 & SYNTHESIZED_WIRE_1);

assign	PPi = SYNTHESIZED_WIRE_2 ^ Negate;


endmodule
