
module shift_and_or(input wire clk, input wire [31:0] in, output wire out);

   // Double-width register to store the concatenation of 'd' and 'in'
   reg [63:0] d_reg;

   // Always-FF block to update the register on the rising edge of the clock
   always @(posedge clk) begin
      d_reg <= {d_reg[31:0], in[0] ? in : 32'b0};
   end

   // Wire to store the result of the OR operation on the lower 39 bits of 'd_reg'
   wire tmp0 = |d_reg[38:0];

   // Final assignment of the output based on the OR operation results
   assign out = d_reg[39] | tmp0;

endmodule