
module d_ff_async_reset(
  input clk,       // clock input
  input d,         // data input
  input r,         // asynchronous reset input
  output reg q     // flip-flop output
);

  always @(posedge clk or posedge r) begin
    if (r) begin
      q <= 1'b0;
    end else begin
      q <= d;
    end
  end

endmodule