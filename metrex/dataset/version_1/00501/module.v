
module SingleCounter(
  input   clock,
  input   reset,
  input   io_input_reset,
  output  io_output_done
);
  reg [5:0] count;
  wire _toggle;

  assign _toggle = (count == 6'd63);
  assign io_output_done = _toggle;

  always @(posedge clock) begin
    if (reset || io_input_reset) begin
      count <= 6'b0;
    end else if (_toggle) begin
      count <= 6'b0;
    end else begin
      count <= count + 1;
    end
  end
endmodule
