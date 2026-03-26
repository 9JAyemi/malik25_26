module comb_circuit (
  input a,
  input b,
  input c,
  output reg out
);

  always @* begin
    case ({a, b})
      2'b11: out = ~c;
      2'b10: out = c;
      2'b01: out = ~c;
      2'b00: out = 1'b0;
    endcase
  end

endmodule
