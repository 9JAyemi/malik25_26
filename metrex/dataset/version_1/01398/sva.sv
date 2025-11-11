// SVA checker for binary_ones_complement
module binary_ones_complement_sva (
  input logic [3:0] B,
  input logic [3:0] C
);

  // Functional equivalence holds at all times
  property p_func;
    C === ~B;
  endproperty
  assert property (p_func)
    else $error("C must equal ~B");

  // When B changes, C reflects ~B in the same time step
  property p_same_timestep_update;
    $changed(B) |-> ##0 (C === ~B);
  endproperty
  assert property (p_same_timestep_update)
    else $error("C not updated to ~B in same timestep after B change");

  // C only changes when B changes (no spurious glitches)
  property p_c_changes_imply_b_changes;
    $changed(C) |-> $changed(B);
  endproperty
  assert property (p_c_changes_imply_b_changes)
    else $error("C changed without B changing");

  // If input is known, output is known and correct
  property p_known_io;
    !$isunknown(B) |-> (!$isunknown(C) && (C == ~B));
  endproperty
  assert property (p_known_io)
    else $error("With known B, C must be known and equal ~B");

  // Coverage: observe responsiveness on any input change
  cover property ($changed(B) && (C === ~B));

  // Coverage: hit all 16 input/output combinations
  genvar v;
  generate
    for (v = 0; v < 16; v++) begin : g_all_vals
      localparam logic [3:0] V = v;
      cover property (B == V && C === ~V);
    end
  endgenerate

endmodule

bind binary_ones_complement binary_ones_complement_sva sva_inst (.*);