// SVA bind module for reversed_gate
module reversed_gate_sva (
  input logic        clk,
  input logic [4:0]  ctrl,
  input logic [15:0] din,
  input logic [3:0]  sel,
  input logic [31:0] dout
);

  default clocking cb @(posedge clk); endclocking

  // past-valid guard for $past()
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // Helpers
  let prod     = $unsigned(ctrl) * $unsigned(sel);   // 0..465
  let idx      = 31 - prod;                          // case selector
  let in_range = (prod <= 31);                       // idx in [0..31]
  let mask2    = (32'h3 << idx);                     // 2-bit mask at idx (valid when idx<=30)
  let mask1    = (32'h1 << 31);                      // 1-bit mask at 31

  // For idx in [0..30]: update exactly dout[idx+1:idx] = din[1:0]; all other bits unchanged
  property p_two_bit_update;
    disable iff (!past_valid || $isunknown({ctrl, sel, din}))
      (in_range && (idx <= 30))
      |-> (dout[idx +: 2] == din[1:0])
          && (((dout ^ $past(dout)) & ~mask2) == 32'h0);
  endproperty
  assert property (p_two_bit_update);

  // For idx == 31: update exactly dout[31] = din[0]; all other bits unchanged
  property p_one_bit_update;
    disable iff (!past_valid || $isunknown({ctrl, sel, din}))
      (in_range && (idx == 31))
      |-> (dout[31] == din[0])
          && (((dout ^ $past(dout)) & ~mask1) == 32'h0);
  endproperty
  assert property (p_one_bit_update);

  // When idx is out of range (no case item matches): dout must hold its value
  property p_out_of_range_stable;
    disable iff (!past_valid || $isunknown({ctrl, sel}))
      (!in_range) |-> $stable(dout);
  endproperty
  assert property (p_out_of_range_stable);

  // Functional coverage: hit every reachable idx and the out-of-range condition
  genvar k;
  generate
    for (k = 0; k < 32; k++) begin : C_IDX
      cover property (in_range && (idx == k));
    end
  endgenerate
  cover property (!in_range);

endmodule

// Bind to DUT
bind reversed_gate reversed_gate_sva sva_i (.*);