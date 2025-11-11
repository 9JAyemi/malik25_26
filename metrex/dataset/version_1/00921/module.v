module adder(A, B, reset, clk, sum, carry);

   input [3:0] A;
   input [3:0] B;
   input reset;
   input clk;
   output [3:0] sum;
   output carry;

   reg [3:0] sum_reg;
   reg carry_reg;

   always @(posedge clk) begin
      if (reset) begin
         sum_reg <= 4'b0;
         carry_reg <= 1'b0;
      end
      else begin
         sum_reg <= A + B;
         carry_reg <= (A[3] & B[3]) | (A[3] & ~sum_reg[3]) | (B[3] & ~sum_reg[3]);
      end
   end

   assign sum = sum_reg;
   assign carry = carry_reg;

endmodule