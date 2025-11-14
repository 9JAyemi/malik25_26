module address_filter
  (input clk,
   input reset,
   input go,
   input [7:0] data,
   output match,
   output done);

   reg [2:0] af_state;

   always @(posedge clk)
     if(reset)
       af_state <= 0;
     else if(go)
       if(data[0] == 1'b0)
         af_state <= 1'b0;
       else
         af_state <= 3'b001;
     else
       case(af_state)
         3'b001: af_state <= 3'b010;
         3'b010: af_state <= 3'b011;
         3'b011: af_state <= 3'b100;
         3'b100: af_state <= 3'b101;
         3'b101: af_state <= 3'b110;
         3'b110: af_state <= 3'b000;
         default: af_state <= 3'b000;
       endcase

   assign match = (af_state == 3'b110);
   assign done = (af_state == 3'b110) || (af_state == 3'b000);
   
endmodule