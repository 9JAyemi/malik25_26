
module glitch_filter (
  input in,
  output out,
  input clk
);

  reg delay_line;

  always @(posedge clk) begin
    delay_line <= in;
  end

  assign out = (in == delay_line) ? in : delay_line;

endmodule