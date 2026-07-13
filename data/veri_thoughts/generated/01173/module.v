
module controlALU(
    input [1:0] ALUop,
    input [5:0] instru,
    input clk,
    output reg [2:0]contALU
    );
    
    always @(*)
    begin
		if (ALUop==2'b00)
			begin
			contALU=   3'b010;
			end
	
		else if (ALUop==2'b01)
			begin
			contALU=	3'b110;
			end
		else
			begin
				case (instru)
		
                                              
                6'b100000:contALU=   3'b010;
                6'b100010:contALU=   3'b110;
                6'b100100:contALU=   3'b000;
                6'b100101:contALU=   3'b001;
                6'b101010:contALU=   3'b111;
                default:    contALU=   3'b101;
                endcase
			end
		                   
                 
    end
endmodule
