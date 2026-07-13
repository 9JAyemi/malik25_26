
module dff_asr (
  input  clk,
  input  d,
  input  set,
  input  reset,
  output reg q,
  output reg q_n
);

  always @(posedge clk) begin
    if (set) begin
      q <= 1'b1;
      q_n <= 1'b0;
    end else if (reset) begin
      q <= 1'b0;
      q_n <= 1'b1;
    end else begin
      q <= d;
      q_n <= ~d;
    end
  end

endmodule