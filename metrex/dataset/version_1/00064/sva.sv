// SVA for ones_complement. Focused, clockless, bindable.
`ifndef ONES_COMPLEMENT_SVA_SV
`define ONES_COMPLEMENT_SVA_SV

module ones_complement_sva (input logic [3:0] binary,
                            input logic [3:0] ones_comp);

  // Functional correctness whenever output changes (avoids NBA race).
  property p_correct_on_update;
    @(ones_comp) ones_comp === ~binary;
  endproperty
  assert property (p_correct_on_update)
    else $error("ones_complement mismatch: bin=%0h ones=%0h exp=%0h", binary, ones_comp, ~binary);

  // Stronger: invariant check with deferred immediate assert to align with NBA.
  always @(binary or ones_comp) begin
    assert #0 (ones_comp === ~binary)
      else $error("ones_complement mismatch (deferred): bin=%0h ones=%0h exp=%0h", binary, ones_comp, ~binary);
  end

  // Known-in implies known-out.
  property p_known_in_known_out;
    @(ones_comp) !$isunknown(binary) |-> !$isunknown(ones_comp);
  endproperty
  assert property (p_known_in_known_out);

  // No spurious output changes without an input change since last output change.
  assert property (@(ones_comp) $changed(binary))
    else $error("ones_comp changed without binary changing");

  // Coverage: exercise all 16 input/output mappings (sampled on output update).
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : cov_all_values
      cover property (@(ones_comp)
        (binary === i[3:0]) && (ones_comp === ~i[3:0]));
    end
  endgenerate

  // Coverage: observe each bit pair toggling together at least once.
  genvar b;
  generate
    for (b = 0; b < 4; b++) begin : cov_bit_pairs
      cover property (@(ones_comp) $changed(binary[b]) && $changed(ones_comp[b]));
    end
  endgenerate

endmodule

// Bind into the DUT
bind ones_complement ones_complement_sva u_ones_complement_sva (.*);

`endif