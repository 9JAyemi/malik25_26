module dff2(q, clk, in0, in1, sel0, sel1);
  output reg [1:0] q;
  input clk;
  input [1:0] in0, in1;
  input sel0, sel1;

  always @(posedge clk) begin
    if (sel0) q <= in0;
    else if (sel1) q <= in1;
  end
endmodule

