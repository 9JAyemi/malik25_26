// SVA for binary_priority_decoder
// Bind these assertions to the DUT

module binary_priority_decoder_sva #(parameter int n = 4) ();
  // Bound into DUT scope: can directly see in, priority_bits, out, and internal wires

  // Parameter sanity (this RTL only implements n==4 correctly)
  initial begin
    assert (n == 4)
      else $fatal(1, "binary_priority_decoder: n!=4 is unsupported by current RTL");
  end

  // Golden re-computation (effective behavior for n=4)
  wire [3:0] pe = ~(in ^ priority_bits);
  // Effective mask after concatenation/truncation in RTL
  wire [3:0] mask_eff = {pe[2] & pe[1], pe[2] & pe[0], pe[1] & pe[0], pe[0]};
  wire [3:0] pm_eff   = pe & mask_eff;

  // Structural sanity (n==4)
  always_comb begin
    assert (priority_sorted == priority_encoded)
      else $error("priority_sorted must equal priority_encoded");
    assert (priority_encoded == pe)
      else $error("priority_encoded mismatch");
    assert (priority_mask == mask_eff)
      else $error("priority_mask unexpected for n==4");
    assert (priority_masked == pm_eff)
      else $error("priority_masked mismatch");
  end

  // Functional mapping of case statement
  // If priority_masked is onehot0 (one-hot or zero), out must be |priority_masked
  property p_onehot0_maps;
    $onehot0(pm_eff) |-> (out === (|pm_eff));
  endproperty
  assert property (@(in or priority_bits) p_onehot0_maps);

  // If priority_masked has multiple 1's, out must be X (default branch)
  property p_illegal_multi_hot_gives_x;
    !$onehot0(pm_eff) |-> $isunknown(out);
  endproperty
  assert property (@(in or priority_bits) p_illegal_multi_hot_gives_x);

  // Explicit 1-cases implied by the RTL math
  property p_out1_case_lsb;
    (pe[0] && !pe[1] && !pe[2]) |-> (out === 1'b1);
  endproperty
  assert property (@(in or priority_bits) p_out1_case_lsb);

  property p_out1_case_msb;
    (!pe[0] && pe[1] && pe[2] && pe[3]) |-> (out === 1'b1);
  endproperty
  assert property (@(in or priority_bits) p_out1_case_msb);

  // Out=0 when masked is zero
  property p_out0_when_pm_zero;
    (pm_eff == 4'b0000) |-> (out === 1'b0);
  endproperty
  assert property (@(in or priority_bits) p_out0_when_pm_zero);

  // Coverage
  cover property (@(in or priority_bits) (pm_eff == 4'b0000) && (out === 1'b0));
  cover property (@(in or priority_bits) (pm_eff == 4'b0001) && (out === 1'b1));
  cover property (@(in or priority_bits) (pm_eff == 4'b1000) && (out === 1'b1));
  cover property (@(in or priority_bits) (!$onehot0(pm_eff) && $isunknown(out)));
  cover property (@(in or priority_bits) !$isunknown({in, priority_bits}));
endmodule

bind binary_priority_decoder binary_priority_decoder_sva #(.n(n)) u_sva();