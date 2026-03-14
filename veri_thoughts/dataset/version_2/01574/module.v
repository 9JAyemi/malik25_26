
module dff_en_ce (
  input clk,
  input en,
  input enclk,
  input d,
  output q
);

  reg q_reg;

  always @(posedge clk) begin
    if (enclk) begin
      if (en)
        q_reg <= d;
    end
    else
      q_reg <= q_reg;
  end

  assign q = q_reg;

endmodule