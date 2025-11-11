
module Divisor_Frecuencia (
		input  C_100Mhz, output  C_1Hz
	);

	reg[31:0] contador = 0; reg C_1Hz=0;
	 
	always @(posedge C_100Mhz)
		begin
				if (contador == 50000000-1)          begin
					C_1Hz <= ~C_1Hz;
					contador <=0;
					end
				
				else
					begin
					contador <= contador + 1;        end
	  end
endmodule
