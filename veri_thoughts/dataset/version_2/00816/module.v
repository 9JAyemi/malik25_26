
module DFF(clk, d, q, en, rst);
  input clk, d, en, rst;
  output q;

  reg q_reg;

  always @(posedge clk or posedge rst) begin
    if (rst) begin
      q_reg <= 1'b0;
    end else if (en) begin
      q_reg <= d;
    end
  end

  assign q = q_reg;
endmodule

module BUF(A, Y);
  input A;
  output Y;

  assign Y = A;
endmodule

module Clock_Gating_Circuit (CLK, EN, TE, ENCLK);
  input CLK, EN, TE;
  output ENCLK;
  wire n2, n3;

  DFF latch(.clk(CLK), .d(n3), .q(n2), .en(EN), .rst(1'b0));
  BUF U1(.A(n2), .Y(ENCLK));

  assign n3 = EN & TE;
endmodule
