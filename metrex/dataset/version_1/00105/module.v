
module RegistroWithMuxInput#(parameter Width = 4)
(CLK,EnableRegisterIn,reset,SELCoeffX,SELCoeffY,Coeff00,Coeff01,Coeff02,Coeff03,Coeff04,Coeff05,Coeff06,Coeff07,Coeff08,Coeff09,
Coeff10,Coeff11,Coeff12,Coeff13,Coeff14,Coeff15,Coeff16,Coeff17,Coeff18,Coeff19,OffsetIn,OutCoeffX,OutCoeffY,OffsetOut);

	input signed [Width-1:0] Coeff00,Coeff01,Coeff02,Coeff03,Coeff04,Coeff05,Coeff06,Coeff07,Coeff08,
	Coeff09,Coeff10,Coeff11,Coeff12,Coeff13,Coeff14,Coeff15,Coeff16,Coeff17,Coeff18,Coeff19,OffsetIn;
	
	input CLK,EnableRegisterIn,reset;
	input [3:0] SELCoeffX,SELCoeffY;
	
	output reg signed [Width-1:0] OutCoeffX = 0;
	output reg signed [Width-1:0] OutCoeffY = 0;  output signed [Width-1:0] OffsetOut;
	
	reg signed [Width-1:0] AuxCoeff00,AuxCoeff01,AuxCoeff02,AuxCoeff03,AuxCoeff04,AuxCoeff05,AuxCoeff06,
	AuxCoeff07,AuxCoeff08,AuxCoeff09,AuxCoeff10,AuxCoeff11,AuxCoeff12,AuxCoeff13,AuxCoeff14,AuxCoeff15,AuxCoeff16,
	AuxCoeff17,AuxCoeff18,AuxCoeff19,AuxCoeff20;
	
	always @(posedge CLK)
	  if (reset) begin
		  AuxCoeff00 <= 0;
		  AuxCoeff01 <= 0;
		  AuxCoeff02 <= 0;
		  AuxCoeff03 <= 0;
		  AuxCoeff04 <= 0;
		  AuxCoeff05 <= 0;
		  AuxCoeff06 <= 0;
		  AuxCoeff07 <= 0;
		  AuxCoeff08 <= 0;
		  AuxCoeff09 <= 0;
		  AuxCoeff10 <= 0;
		  AuxCoeff11 <= 0;
		  AuxCoeff12 <= 0;
		  AuxCoeff13 <= 0;
		  AuxCoeff14 <= 0;
		  AuxCoeff15 <= 0;
		  AuxCoeff16 <= 0;
		  AuxCoeff17 <= 0;
		  AuxCoeff18 <= 0;
		  AuxCoeff19 <= 0;
		  AuxCoeff20 <= 0;
	  end else if (EnableRegisterIn) begin
		  AuxCoeff00 <= Coeff00;
		  AuxCoeff01 <= Coeff01;
		  AuxCoeff02 <= Coeff02;
		  AuxCoeff03 <= Coeff03;
		  AuxCoeff04 <= Coeff04;
		  AuxCoeff05 <= Coeff05;
		  AuxCoeff06 <= Coeff06;
		  AuxCoeff07 <= Coeff07;
		  AuxCoeff08 <= Coeff08;
		  AuxCoeff09 <= Coeff09;
		  AuxCoeff10 <= Coeff10;
		  AuxCoeff11 <= Coeff11;
		  AuxCoeff12 <= Coeff12;
		  AuxCoeff13 <= Coeff13;
		  AuxCoeff14 <= Coeff14;
		  AuxCoeff15 <= Coeff15;
		  AuxCoeff16 <= Coeff16;
		  AuxCoeff17 <= Coeff17;
		  AuxCoeff18 <= Coeff18;
		  AuxCoeff19 <= Coeff19;
		  AuxCoeff20 <= OffsetIn;
	  end
	  
	  assign OffsetOut = AuxCoeff20;
	  
	  always @(SELCoeffX, AuxCoeff00,AuxCoeff01,AuxCoeff02,AuxCoeff03,AuxCoeff04,AuxCoeff05,AuxCoeff06,
		AuxCoeff07,AuxCoeff08,AuxCoeff09)
      case (SELCoeffX)
         5'd00: OutCoeffX <= AuxCoeff00;
         5'd01: OutCoeffX <= AuxCoeff01;
         5'd02: OutCoeffX <= AuxCoeff02;
         5'd03: OutCoeffX <= AuxCoeff03;
         5'd04: OutCoeffX <= AuxCoeff04;
         5'd05: OutCoeffX <= AuxCoeff05;
         5'd06: OutCoeffX <= AuxCoeff06;
         5'd07: OutCoeffX <= AuxCoeff07;
			5'd08: OutCoeffX <= AuxCoeff08;
         5'd09: OutCoeffX <= AuxCoeff09;	
			default : OutCoeffX <= 0;
      endcase
		
		always @(SELCoeffY,AuxCoeff10,AuxCoeff11,AuxCoeff12,AuxCoeff13,AuxCoeff14,AuxCoeff15,AuxCoeff16,
		AuxCoeff17,AuxCoeff18,AuxCoeff19)
      case (SELCoeffY)
         5'd00: OutCoeffY <= AuxCoeff10;
         5'd01: OutCoeffY <= AuxCoeff11;
         5'd02: OutCoeffY <= AuxCoeff12;
         5'd03: OutCoeffY <= AuxCoeff13;
         5'd04: OutCoeffY <= AuxCoeff14;
         5'd05: OutCoeffY <= AuxCoeff15;
         5'd06: OutCoeffY <= AuxCoeff16;
         5'd07: OutCoeffY <= AuxCoeff17;
			5'd08: OutCoeffY <= AuxCoeff18;
         5'd09: OutCoeffY <= AuxCoeff19;	
			default : OutCoeffY <= 0;
      endcase


endmodule

