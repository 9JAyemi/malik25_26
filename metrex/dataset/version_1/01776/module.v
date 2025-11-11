
module dff_en(clk, d, en, q, q_bar);
  input clk, d, en;
  output q, q_bar;

  wire q_next;
  assign q_next = en ? d : q;

  dff dff_inst(.clk(clk), .d(q_next), .q(q), .q_bar(q_bar));
endmodule
module dff(clk, d, q, q_bar);
  input clk, d;
  output q, q_bar;

  reg q;
  assign q_bar = ~q;

  always @(posedge clk) begin
    q <= d;
  end
endmodule