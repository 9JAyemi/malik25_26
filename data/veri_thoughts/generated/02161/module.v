
module sourceMod
  (
   output reg validData,
   input ctrl_clk,
   input ctrl_data
   );

   always @(posedge ctrl_clk) begin
      validData <= ~validData;
   end

endmodule
