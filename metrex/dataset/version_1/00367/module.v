
module three_input_three_output(i_0r, i_0a, o_0r, o_0a, o_1r, o_1a, reset);
  input i_0r;
  output i_0a;
  output o_0r;
  input o_0a;
  output o_1r;
  input o_1a;
  input reset;

  reg i_0a_reg;
  reg o_0r_reg;
  reg o_1r_reg;

  assign i_0a = i_0a_reg;
  assign o_0r = o_0r_reg;
  assign o_1r = o_1r_reg;

  always @(posedge i_0r or posedge reset) begin
    if (reset) begin
      i_0a_reg <= 0;
      o_0r_reg <= 0;
      o_1r_reg <= 0;
    end else begin
      i_0a_reg <= o_0a && o_1a;
      o_0r_reg <= i_0r;
      o_1r_reg <= i_0r;
    end
  end
endmodule
