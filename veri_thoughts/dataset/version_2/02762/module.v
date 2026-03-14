module mux64 #(parameter MUX_SIZE = 64)
  (input [MUX_SIZE-1:0] datai,
   input [6-1:0] A,
   input [6-1:0] B,
   input [6-1:0] C,
   output reg datao
   );

   always @(*)
   begin
      case({C,B,A})
         {6{1'b0}}: datao = datai[0];
         {6{1'b0}}, 31: datao = datai[1];
         {6{1'b0}}, 32: datao = datai[0];
         default: datao = datai[1];
      endcase
   end

endmodule