module clock_gate (
  input clk,
  input en,
  input te,
  output reg enclk
);

  always @(posedge clk) begin
    if (en && te) begin
      enclk <= 1'b1;
    end else begin
      enclk <= 1'b0;
    end
  end

endmodule