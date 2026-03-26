module Score(				RESET,
	SCORE,
	DISP_SU,
	DISP_SD,
	DISP_SC,
	DISP_SM
);
	
	input RESET;			input [11:0] SCORE;			output reg [6:0] DISP_SU;		output reg [6:0] DISP_SD;		output reg [6:0] DISP_SC;		output reg [6:0] DISP_SM;		reg [3:0] SCORE_U;		reg [3:0] SCORE_D;		reg [3:0] SCORE_C;		reg [3:0] SCORE_M;		integer i;				always@(SCORE or RESET) begin
    
	if(RESET==1) begin
	 SCORE_U=0;
    SCORE_D=0;
    SCORE_C=0;
    SCORE_M=0;
	 DISP_SU=0;
	 DISP_SD=0;
	 DISP_SC=0;
	 DISP_SM=0;
	 i=0;
	end
	else begin
  	SCORE_U=0;
    SCORE_D=0;
    SCORE_C=0;
    SCORE_M=0;
	 
	 SCORE_M = SCORE / 1000;
	 SCORE_C = (SCORE - SCORE_M*1000) / 100;
	 SCORE_D = ((SCORE - SCORE_M*1000) - SCORE_C*100) / 10;
	 SCORE_U = ((SCORE - SCORE_M*1000) - SCORE_C*100) - SCORE_D*10;
	 
    
	 
    case (SCORE_M) 0: DISP_SM = 7'b1111110;
      1: DISP_SM = 7'b0110000;
      2: DISP_SM = 7'b1101101;
      3: DISP_SM = 7'b1111001;
      4: DISP_SM = 7'b0110011;
      5: DISP_SM = 7'b1011011;
      6: DISP_SM = 7'b1011111;
      7: DISP_SM = 7'b1110000;
      8: DISP_SM = 7'b1111111;
      9: DISP_SM = 7'b1111011;
      default: DISP_SM = 7'b0000000; 
	  endcase
    case (SCORE_C) 0: DISP_SC = 7'b1111110;
      1: DISP_SC = 7'b0110000;
      2: DISP_SC = 7'b1101101;
      3: DISP_SC = 7'b1111001;
      4: DISP_SC = 7'b0110011;
      5: DISP_SC = 7'b1011011;
      6: DISP_SC = 7'b1011111;
      7: DISP_SC = 7'b1110000;
      8: DISP_SC = 7'b1111111;
      9: DISP_SC = 7'b1111011;
      default: DISP_SC = 7'b0000000; 
	  endcase
    case (SCORE_D) 0: DISP_SD = 7'b1111110;
      1: DISP_SD = 7'b0110000;
      2: DISP_SD = 7'b1101101;
      3: DISP_SD = 7'b1111001;
      4: DISP_SD = 7'b0110011;
      5: DISP_SD = 7'b1011011;
      6: DISP_SD = 7'b1011111;
      7: DISP_SD = 7'b1110000;
      8: DISP_SD = 7'b1111111;
      9: DISP_SD = 7'b1111011;
      default: DISP_SD = 7'b0000000; 
	  endcase
    case (SCORE_U) 0: DISP_SU = 7'b1111110;
      1: DISP_SU = 7'b0110000;
      2: DISP_SU = 7'b1101101;
      3: DISP_SU = 7'b1111001;
      4: DISP_SU = 7'b0110011;
      5: DISP_SU = 7'b1011011;
      6: DISP_SU = 7'b1011111;
      7: DISP_SU = 7'b1110000;
      8: DISP_SU = 7'b1111111;
      9: DISP_SU = 7'b1111011;
      default: DISP_SU = 7'b0000000; 
	  endcase
  end
 end
endmodule
	