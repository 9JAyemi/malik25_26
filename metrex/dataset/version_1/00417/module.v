module d_ff_async_reset(clk, reset, d, q);
  input clk, reset, d;
  output q;

  reg q;

  always @(posedge clk, negedge reset) begin
    if (!reset) begin
      q <= 1'b0;
    end else begin
      q <= d;
    end
  end

endmodule