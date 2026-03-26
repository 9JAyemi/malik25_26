module Test (
   input [3:0] cnt,
   input [6:0] decr,
   output [3:0] next
);

   // Implement the Test module here
   reg [3:0] next_reg;

   always @(*) begin
      next_reg = cnt ^ decr[3:0];
   end

   assign next = next_reg;

endmodule

