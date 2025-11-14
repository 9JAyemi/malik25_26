
module d_ff_en(clk, en, te, d, enclk);
  input clk, en, te, d;
  output reg enclk;
  reg q;

  always @(posedge clk) begin
    if (en) begin
      q <= d;
      enclk <= 1'b1;
    end else begin
      enclk <= 1'b0;
    end
  end
  
  always @(posedge te) begin
    q <= q;
  end

endmodule