
module t_flip_flop(input t, input clk, output reg q);

  always @(posedge clk) begin
    q <= q ^ t;
  end

endmodule
