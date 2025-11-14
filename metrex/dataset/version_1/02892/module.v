
module my_module (
   input in,
   input clk,
   output reg fr_a,
   output reg fr_b,
   output reg fr_chk
   );

   always @(posedge clk) begin
      fr_a <= in;
      fr_b <= in;
      fr_chk <= in + 1;
   end

endmodule