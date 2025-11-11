
module multiplicadorPuntoFijo  #(parameter Width = 24, Magnitud = 4, Precision = 19, Signo = 1)
		(EnableMul,In,Coeff,OutMul,Error);
	 
	 input EnableMul;
	 input signed [Width-1:0] In,Coeff;
	 output reg signed [Width-1:0] OutMul = 0; 
	 output Error;
	 reg signed [2*Width-1:0]  AuxMul = 0; 
	 reg Overflow = 0;
	 reg Underflow = 0;
	 
	 
	 
		always @* begin if (EnableMul) begin
				AuxMul <= In * Coeff; end
			else begin
				AuxMul <= 0;
			end
		end
		
		always @* begin if (~In[Width-1] && ~Coeff[Width-1] && AuxMul[2*Width -1 - Magnitud - Signo]) begin
				Overflow <= 1;
				Underflow <= 0;
			end
			else if(In[Width-1] && Coeff[Width-1] && AuxMul[2*Width -1 - Magnitud - Signo]) begin
				Overflow <= 1;
				Underflow <= 0;
			end
			else if(~In[Width-1] && Coeff[Width-1] && ~AuxMul[2*Width -1 - Magnitud - Signo]) begin
				Overflow <= 0;
				Underflow <= 1;
			end
			else if(In[Width-1] && ~Coeff[Width-1] && ~AuxMul[2*Width -1 - Magnitud - Signo]) begin
				Overflow <= 0;
				Underflow <= 1;
			end
			else begin
				Overflow <= 0;
				Underflow <= 0;
			end
		end
		
		always @* begin if (In == 0 || Coeff==0) begin
					OutMul <= 0;
			end 
			else begin
				if (Overflow) begin
					OutMul <= 2**(Width-1) -1;  end
				else begin
					if (Underflow) begin
						OutMul <= -2**(Width-1);    end
					else begin
						OutMul <= AuxMul[2*Width -1 - Magnitud - Signo : Precision];      end
				end	
			end
		end
		
		assign Error =  Overflow | Underflow;
		
	
	 endmodule
