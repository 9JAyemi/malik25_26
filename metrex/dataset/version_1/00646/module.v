module Test (
   input clk,
   input [63:0] rc,
   output reg o
);

   reg [63:0] rc_next;

   // Calculate rc_next
   always @ (posedge clk) begin
      rc_next <= {rc[62:0], rc[63] ^ rc[2] ^ rc[0]};
   end

   // Calculate o
   always @ (posedge clk) begin
      o <= (rc[0] ^ rc[1]) & (rc[62] ^ rc[63]);
   end

endmodule