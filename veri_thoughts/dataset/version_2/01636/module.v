module button_counter (
   input  wire        BTN,
   output reg  [3:0]  COUNT
);

   always @(posedge BTN) begin
      if (COUNT == 15)
         COUNT <= 0;
      else
         COUNT <= COUNT + 1;
   end
   
endmodule