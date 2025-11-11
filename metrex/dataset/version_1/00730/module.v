
module EscrituraRegistroToMemoria#(parameter Width = 4)
(Read,InError,Address,ListoIn,InDato,Coeff00,Coeff01,Coeff02,Coeff03,Coeff04,Coeff05,
Coeff06,Coeff07,Coeff08,Coeff09,Coeff10,Coeff11,Coeff12,Coeff13,Coeff14,Coeff15,Coeff16,Coeff17,Coeff18,
Coeff19,Offset,DatoEntradaSistema,Y0,Y1,Y2,Y3,Y4,Y5,Y6,Y7,Y8,Y9,OutDato);
	 
	input Read,InError,ListoIn;
   input [8:0] Address; 
	input signed [Width-1:0] InDato,Coeff00,Coeff01,Coeff02,Coeff03,Coeff04,Coeff05,
   Coeff06,Coeff07,Coeff08,Coeff09,Coeff10,Coeff11,Coeff12,Coeff13,Coeff14,Coeff15,Coeff16,
	Coeff17,Coeff18,Coeff19,Offset,DatoEntradaSistema,Y0,Y1,Y2,Y3,Y4,Y5,Y6,Y7,Y8,Y9;
	
	output reg signed [Width-1:0] OutDato;

	always @*begin if(Read) begin
			if(Address==9'h000 && ListoIn==1'b1) begin  OutDato <= 1; 
			end else if(Address==9'h004 ) begin  OutDato <= InDato; 
			end else if(Address==9'h008 && InError==1'b1) begin   OutDato <= 1;
			end else if(Address==9'h00C ) begin   OutDato <= Coeff00;
			end else if(Address==9'h010 ) begin   OutDato <= Coeff01;
			end else if(Address==9'h014 ) begin   OutDato <= Coeff02;
			end else if(Address==9'h018 ) begin   OutDato <= Coeff03;
			end else if(Address==9'h01C ) begin   OutDato <= Coeff04;
			end else if(Address==9'h020 ) begin   OutDato <= Coeff05;
			end else if(Address==9'h024 ) begin   OutDato <= Coeff06;
			end else if(Address==9'h028 ) begin   OutDato <= Coeff07;
			end else if(Address==9'h02C ) begin   OutDato <= Coeff08;
			end else if(Address==9'h030 ) begin   OutDato <= Coeff09;
			end else if(Address==9'h034 ) begin   OutDato <= Coeff10;
			end else if(Address==9'h038 ) begin   OutDato <= Coeff11;
			end else if(Address==9'h03C ) begin   OutDato <= Coeff12;
			end else if(Address==9'h040 ) begin   OutDato <= Coeff13;
			end else if(Address==9'h044 ) begin   OutDato <= Coeff14;
			end else if(Address==9'h048 ) begin   OutDato <= Coeff15;
			end else if(Address==9'h04C ) begin   OutDato <= Coeff16;
			end else if(Address==9'h050 ) begin   OutDato <= Coeff17;
			end else if(Address==9'h054 ) begin   OutDato <= Coeff18;
			end else if(Address==9'h058 ) begin   OutDato <= Coeff19;
			end else if(Address==9'h05C ) begin   OutDato <= Offset;
			end else if(Address==9'h060 ) begin   OutDato <= DatoEntradaSistema;
			end else if(Address==9'h064 ) begin   OutDato <= Y0;
			end else if(Address==9'h068 ) begin   OutDato <= Y1;
			end else if(Address==9'h06C ) begin   OutDato <= Y2;
			end else if(Address==9'h070 ) begin   OutDato <= Y3;
			end else if(Address==9'h074 ) begin   OutDato <= Y4;
			end else if(Address==9'h078 ) begin   OutDato <= Y5;
			end else if(Address==9'h07C ) begin   OutDato <= Y6;
			end else if(Address==9'h080 ) begin   OutDato <= Y7;
			end else if(Address==9'h084 ) begin   OutDato <= Y8;
			end else if(Address==9'h088 ) begin   OutDato <= Y9;	
			end else begin
				OutDato <= 0;
			end
		end
		else begin
			OutDato <= 0;
		end
	end
endmodule

