module clock_divider (
  input     clkin,
  input     reset,
  output    clkoutp,
  output    clkoutn
);

  parameter clkdiv = 2;

  reg       clkbase;
  reg [6:0] clkcnt;

  assign clkoutp = ~clkbase;
  assign clkoutn = clkbase;

  always @(posedge clkin or negedge reset) begin
    if (~reset) begin
      clkcnt  <= 0;
      clkbase <= 0;
    end else begin
      if (clkcnt == clkdiv-1) begin
        clkcnt  <= 0;
        clkbase <= ~clkbase;
      end else begin
        clkcnt <= clkcnt + 1;
      end
    end
  end

endmodule