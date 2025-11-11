// SVA for DAC. Bind this file to the DUT.
// Notes:
// - a_out_is_lsb intentionally checks the 1-bit truncation of analog_voltage to analog_out.
// - If you later widen analog_out or fix resistor_values, revisit related assertions.

module DAC_SVA #(parameter int N = 8) (
  input  logic              clk,
  input  logic              rst,
  input  logic [N-1:0]      din,
  input  logic [N-1:0]      binary_value,
  input  logic [N-1:0]      resistor_values,
  input  logic [31:0]       analog_voltage,
  input  logic              analog_out
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Elaboration-time sanity (concise, catches common intent issues)
  initial begin
    assert (N == 8)
      else $error("DAC_SVA: Parameter n (%0d) differs from expected 8 used by DUT concatenation.", N);
    assert ($bits(analog_out) == 1)
      else $error("DAC_SVA: analog_out is not 1-bit; update truncation-related checks.");
  end

  // Reset: clears and holds register to zero
  assert property (@cb rst |=> (binary_value == '0)) else $error("binary_value not cleared after reset.");
  assert property (@cb rst |->  (binary_value == '0)) else $error("binary_value not held at zero during reset.");

  // Register capture: 1-cycle latency from din to binary_value
  assert property (@cb binary_value == $past(din))
    else $error("binary_value != $past(din) when not in reset.");

  // Combinational mappings (as coded in DUT)
  assert property (@cb analog_voltage == (binary_value * resistor_values))
    else $error("analog_voltage mismatch with binary_value * resistor_values.");
  assert property (@cb analog_out == analog_voltage[0])
    else $error("analog_out is not equal to LSB of analog_voltage (possible truncation mismatch).");

  // Static resistor ladder value should not change at runtime
  assert property (@cb $stable(resistor_values))
    else $error("resistor_values changed after elaboration.");

  // Mid-cycle stability (no glitches between clock edges)
  assert property (@(negedge clk) $stable(analog_voltage) && $stable(analog_out))
    else $error("analog paths glitching between clocks.");

  // Monotonicity: linear mapping wrt din
  assert property (@cb ($past(din) <  din) |-> ($past(analog_voltage) <  analog_voltage))
    else $error("Non-monotonic increase: din up but analog_voltage not up.");
  assert property (@cb ($past(din) >  din) |-> ($past(analog_voltage) >  analog_voltage))
    else $error("Non-monotonic decrease: din down but analog_voltage not down.");

  // No X propagation after reset deasserts
  assert property (@cb !$isunknown({din, binary_value, resistor_values, analog_voltage, analog_out}))
    else $error("Unknown (X/Z) detected on DAC signals.");

  // Coverage
  cover property (@cb rst ##1 !rst);                              // reset deassert sequence
  cover property (@cb din == '0);                                 // min code
  cover property (@cb din == {N{1'b1}});                          // max code
  cover property (@cb $rose(analog_out));                         // toggle high
  cover property (@cb $fell(analog_out));                         // toggle low
  cover property (@cb (din == '0) ##1 (din == '0 + 1) ##1 (din == '0 + 2)); // small upward ramp

endmodule

// Bind to all DAC instances; parameter N follows DUT parameter n.
bind DAC DAC_SVA #(.N(n)) u_dac_sva (
  .clk(clk),
  .rst(rst),
  .din(din),
  .binary_value(binary_value),
  .resistor_values(resistor_values),
  .analog_voltage(analog_voltage),
  .analog_out(analog_out)
);