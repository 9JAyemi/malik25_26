
module DAC (
  input clk,
  input rst,
  input [n-1:0] din,
  output analog_out
);

parameter n = 8; // number of bits in the digital input signal
parameter v_ref_int = 32'd1000; // reference voltage for the DAC in mV
parameter v_ref = v_ref_int / 1000.0; // reference voltage for the DAC in V

reg [n-1:0] binary_value;
wire [n-1:0] resistor_values;
wire [31:0] analog_voltage;

assign resistor_values = {v_ref_int, v_ref_int>>1, v_ref_int>>2, v_ref_int>>3, v_ref_int>>4, v_ref_int>>5, v_ref_int>>6, v_ref_int>>7}; // weighted resistor values

assign analog_voltage = binary_value * resistor_values; // digital-to-analog conversion

always @(posedge clk) begin
  if (rst) begin
    binary_value <= 0; // reset to zero volts
  end else begin
    binary_value <= din; // update binary value
  end
end

assign analog_out = analog_voltage;

endmodule