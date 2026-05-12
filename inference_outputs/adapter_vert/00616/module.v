
module FFType(
  input   clock,
  input   reset,
  input   io_in,
  input   io_init,
  output  io_out,
  input   io_enable
);
  reg  d;

  assign io_out = d;
  always @(posedge clock) begin
    if (reset) begin
      d <= io_init;
    end else if (io_enable) begin
      d <= io_in;
    end
  end

endmodule