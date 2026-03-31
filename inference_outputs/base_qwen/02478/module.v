module sync_up_down_counter (
  input clk,
  input up_down,
  output reg [2:0] q
);

  always @(posedge clk) begin
    if (up_down == 0) begin
      if (q == 7)
        q <= 0;
      else
        q <= q + 1;
    end else begin
      if (q == 0)
        q <= 7;
      else
        q <= q - 1;
    end
  end

endmodule
