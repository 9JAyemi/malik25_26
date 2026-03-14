
module crc_module (
   // Inputs
   clk,
   // Outputs
   Output
   );

   input clk;
   output reg [8:0] Output;

   integer cyc; initial cyc = 0;
   reg [63:0] crc;
   reg [31:0] sum;

   wire [8:0] Input = crc[8:0];

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
      if (cyc==0) begin
         // Setup
         crc <= 64'h5aef0c8d_d70a4497;
         sum <= 32'h0;
      end
      else if (cyc>10 && cyc<90) begin
         sum <= {sum[30:0],sum[31]} ^ {23'h0, crc[8:0]};
      end
      else if (cyc==99) begin
         if (sum == 32'he8bbd130) begin
            Output <= 9'h4a;
         end
         else begin
            Output <= 9'h55;
         end
      end
   end

endmodule