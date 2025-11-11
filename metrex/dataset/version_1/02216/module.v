
module unsigned_non_restoring_divider (
  input [N-1:0] dividend,
  input [N-1:0] divisor,
  input clk,
  input rst,
  output [N-1:0] quotient,
  output [N-1:0] remainder
);

parameter N = 8; // number of bits for dividend and divisor

reg [N-1:0] dividend_reg;
reg [N-1:0] divisor_reg;
reg [N-1:0] quotient_reg;
reg [N-1:0] remainder_reg;
reg [N-1:0] dividend_shift_reg;
reg [N:0] counter_reg;

always @(posedge clk) begin
  if (rst) begin
    dividend_reg <= 0;
    divisor_reg <= 0;
    quotient_reg <= 0;
    remainder_reg <= 0;
    dividend_shift_reg <= {dividend, 1'b0};
    counter_reg <= N+1;
  end
  else begin
    dividend_reg <= dividend_shift_reg[N-1:0];
    divisor_reg <= divisor;
    if (counter_reg == 0) begin
      remainder_reg <= dividend_shift_reg[N-1:0];
      quotient_reg <= quotient_reg << 1 | dividend[N-1];
      dividend_shift_reg <= {dividend, 1'b0};
      counter_reg <= N+1;
    end
    else begin
      if (remainder_reg >= divisor_reg) begin
        remainder_reg <= remainder_reg - divisor_reg;
        quotient_reg <= quotient_reg | 1<<(counter_reg-1);
      end
      else begin
        quotient_reg <= quotient_reg | 0<<(counter_reg-1);
      end
      counter_reg <= counter_reg - 1;
    end
  end
end

assign quotient = quotient_reg;
assign remainder = remainder_reg;

endmodule