
module fifo (
   // Outputs
   out0, out1,
   // Inputs
   clk, wr0a, wr0b, wr1a, wr1b, inData
);

   input         clk;
   input         wr0a;
   input         wr0b;
   input         wr1a;
   input         wr1b;
   input [15:0]  inData;

   output [15:0] out0;
   output [15:0] out1;

   reg [15:0]    mem [1:0];


   assign        out0 = mem[0];
   assign        out1 = mem[1];

   always @(posedge clk) begin
      // These mem assignments must be done in order after processing
      if (wr0a) begin
         mem[0] <=  inData;
      end
      if (wr0b) begin
         mem[0] <= ~inData;
      end
      if (wr1a) begin
         mem[1] <=  inData;
      end
      if (wr1b) begin
         mem[1] <= ~inData;
      end
   end

endmodule