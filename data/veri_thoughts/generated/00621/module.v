
module spdu_13 (in0, in1, in2, in3, d0, d1, d2, d3, clk, reset, out0, out1, out2, out3);
  input in0, in1, in2, in3, d0, d1, d2, d3, clk, reset;
  output out0, out1, out2, out3;
  wire n1, n2, n3, n4;

  reg out3_reg;
  reg out2_reg;
  reg out1_reg;
  reg out0_reg;

  always @(posedge clk or posedge reset) begin
    if (reset) begin
      out3_reg <= 1'b0;
      out2_reg <= 1'b0;
      out1_reg <= 1'b0;
      out0_reg <= 1'b0;
    end else begin
      out3_reg <= ~((d3 & in3) | (~d3 & in2));
      out2_reg <= ~((d2 & in1) | (~d2 & in0));
      out1_reg <= ~((d1 & in3) | (~d1 & in2));
      out0_reg <= ~((reset) | (d0 & in1) | (~d0 & in0));
    end
  end

  assign out3 = out3_reg;
  assign out2 = out2_reg;
  assign out1 = out1_reg;
  assign out0 = out0_reg;
endmodule