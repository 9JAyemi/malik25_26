// SVA for binary_converter. Bind this to the DUT.
// Focuses on functional correctness, internal wiring, and coverage.

module binary_converter_sva
(
  input logic        signal,
  input logic        inv_signal,
  input logic [9:0]  xor_output,
  input logic [9:0]  adder_output,
  input logic [9:0]  binary_code
);

  default clocking cb @(posedge signal or negedge signal); endclocking
  default disable iff ($isunknown(signal));

  // Sanity: no X on critical nets
  a_known:        assert property (!$isunknown({signal,inv_signal,xor_output,adder_output,binary_code}));

  // Inversion
  a_inv:          assert property (inv_signal === ~signal);

  // XOR mapping as implemented (note width truncation of constants in RTL)
  a_xor_b0:       assert property (xor_output[0]  === inv_signal);
  a_xor_b1:       assert property (xor_output[1]  === ~inv_signal);
  a_xor_hi:       assert property (xor_output[9:2]=== {8{inv_signal}});

  // Adder and output path
  a_add:          assert property (adder_output === (xor_output + 10'd1));
  a_out_path:     assert property (binary_code  === adder_output);

  // End-to-end functional mapping
  a_func:         assert property (binary_code  === (signal ? 10'h003 : 10'h3FE));

  // Coverage
  c_sig0:         cover  property (!signal && binary_code==10'h3FE);
  c_sig1:         cover  property ( signal && binary_code==10'h003);
  c_rise:         cover  property ($rose(signal));
  c_fall:         cover  property ($fell(signal));

endmodule

bind binary_converter binary_converter_sva
(
  .signal(signal),
  .inv_signal(inv_signal),
  .xor_output(xor_output),
  .adder_output(adder_output),
  .binary_code(binary_code)
);