// SVA for flash_ADC
// Bind these checkers to the DUT; focuses on correctness, encoding, and sampling

module flash_ADC_sva(
  input logic        clk,
  input logic [9:0]  Vin,
  input logic [7:0]  Dout,
  input logic [7:0]  ref_voltages,
  input logic [7:0]  comparator_outputs
);

  default clocking cb @(posedge clk); endclocking
  default disable iff ($isunknown(clk));

  // guard for $past
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // helper: exact compare bit the RTL computes (accounting for its width behavior)
  function automatic logic cmp_bit_from_vin (input logic [9:0] v);
    logic [15:0] lhs, rhs;
    begin
      lhs = {8{v[1:0]}};
      rhs = {8'h00, v[9:2]};
      return (lhs > rhs);
    end
  endfunction

  // X checks at sample
  a_no_x: assert property (!$isunknown(Vin) && !$isunknown(Dout)
                           && !$isunknown(ref_voltages) && !$isunknown(comparator_outputs));

  // ref_voltages must be truncation of replicated Vin[9:2] -> equals Vin[9:2]
  a_ref_trunc: assert property (ref_voltages == Vin[9:2]);

  // comparator_outputs must be 8'h00 or 8'h01 with LSB = compare result
  a_cmp_val:   assert property (comparator_outputs == {7'b0, cmp_bit_from_vin(Vin)});
  a_cmp_legal: assert property (comparator_outputs inside {8'h00, 8'h01});

  // Dout is a registered sample of comparator_outputs (previous cycle) and legal
  a_dout_reg:  assert property (disable iff (!past_valid)
                                Dout == {7'b0, cmp_bit_from_vin($past(Vin))});
  a_dout_legal:assert property (Dout inside {8'h00, 8'h01});

  // No mid-cycle glitches on Dout
  a_no_midcycle_glitch: assert property (@(negedge clk) $stable(Dout));

  // Coverage
  c_cmp0: cover property (disable iff (!past_valid) !cmp_bit_from_vin($past(Vin)));
  c_cmp1: cover property (disable iff (!past_valid)  cmp_bit_from_vin($past(Vin)));
  c_eq:   cover property (disable iff (!past_valid)
                          {8{$past(Vin[1:0])}} == {8'h00, $past(Vin[9:2])});
  c_rise: cover property ($rose(Dout[0]));
  c_fall: cover property ($fell(Dout[0]));

endmodule

bind flash_ADC flash_ADC_sva sva_flash_adc (
  .clk(clk),
  .Vin(Vin),
  .Dout(Dout),
  .ref_voltages(ref_voltages),
  .comparator_outputs(comparator_outputs)
);