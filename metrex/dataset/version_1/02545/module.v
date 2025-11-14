module Decodificador(
   input [6:0] Cuenta,
   output reg [7:0] catodo1,
   output reg [7:0] catodo2,
   output reg [7:0] catodo3,
   output reg [7:0] catodo4
);

   always @(*)
   begin
      case (Cuenta)
         7'b0000000: begin
                        catodo1 <= 8'b00000011;
                        catodo2 <= 8'b00000011;
                        catodo3 <= 8'b00000011;
                        catodo4 <= 8'b00000011;
                     end 
         7'b0000001: begin
                        catodo1 <= 8'b10011111;
                        catodo2 <= 8'b00000011;
                        catodo3 <= 8'b00000011;
                        catodo4 <= 8'b00000011; 
                     end 
         7'b0000010: begin
                        catodo1 <= 8'b00100101;
                        catodo2 <= 8'b00000011;
                        catodo3 <= 8'b00000011;
                        catodo4 <= 8'b00000011;
                     end 
         7'b0000011: begin
                        catodo1 <= 8'b00001101;
                        catodo2 <= 8'b00000011;
                        catodo3 <= 8'b00000011;
                        catodo4 <= 8'b00000011;
                     end 
         7'b0000100: begin
                        catodo1 <= 8'b10011001;
                        catodo2 <= 8'b00000011;
                        catodo3 <= 8'b00000011;
                        catodo4 <= 8'b00000011;
                     end 
         7'b0000101: begin
                        catodo1 <= 8'b01001001;
                        catodo2 <= 8'b00000011;
                        catodo3 <= 8'b00000011;
                        catodo4 <= 8'b00000011;
                     end 
         7'b0000110: begin
                        catodo1 <= 8'b01000001;
                        catodo2 <= 8'b00000011;
                        catodo3 <= 8'b00000011;
                        catodo4 <= 8'b00000011;
                     end 
         7'b0000111: begin
                        catodo1 <= 8'b00011111;
                        catodo2 <= 8'b00000011;
                        catodo3 <= 8'b00000011;
                        catodo4 <= 8'b00000011;
                     end 
         7'b0001000: begin
                        catodo1 <= 8'b00000001;
                        catodo2 <= 8'b00000011;
                        catodo3 <= 8'b00000011;
                        catodo4 <= 8'b00000011;
                     end 
         7'b0001001: begin
                        catodo1 <= 8'b00011001;
                        catodo2 <= 8'b00000011;
                        catodo3 <= 8'b00000011;
                        catodo4 <= 8'b00000011;
                     end 
         7'b0001010: begin
                        catodo1 <= 8'b00000011;
                        catodo2 <= 8'b10011111;
                        catodo3 <= 8'b00000011;
                        catodo4 <= 8'b00000011;
                     end 
         7'b0001011: begin
                        catodo1 <= 8'b10011111;
                        catodo2 <= 8'b10011111;
                        catodo3 <= 8'b00000011;
                        catodo4 <= 8'b00000011;
                     end 
         7'b0001100: begin
                        catodo1 <= 8'b00100101;
                        catodo2 <= 8'b10011111;
                        catodo3 <= 8'b00000011;
                        catodo4 <= 8'b00000011;
                     end 
         7'b0001101: begin
                        catodo1 <= 8'b00001101;
                        catodo2 <= 8'b10011111;
                        catodo3 <= 8'b00000011;
                        catodo4 <= 8'b00000011;
                     end 
         7'b0001110: begin
                        catodo1 <= 8'b10011001;
                        catodo2 <= 8'b10011111;
                        catodo3 <= 8'b00000011;
                        catodo4 <= 8'b00000011;
                     end 
         7'b0001111: begin
                        catodo1 <= 8'b01001001;
                        catodo2 <= 8'b10011111;
                        catodo3 <= 8'b00000011;
                        catodo4 <= 8'b00000011;
                     end 
         default:    begin
                        catodo1 <= 8'b10011111;
                        catodo2 <= 8'b10011111;
                        catodo3 <= 8'b10011111; 
                        catodo4 <= 8'b10011111;
                     end 	
      endcase		
   end	 
   
endmodule