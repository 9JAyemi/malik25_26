// SVA for my_module
module my_module_sva (input logic A, TE_B, Z);

  // Functional equivalence (4-state aware, race-safe)
  always_comb begin
    assert (#0 (Z === (TE_B ? 1'b1 : A)))
      else $error("my_module: Z != (TE_B ? 1 : A)");
  end

  // If inputs known, output must be known
  always_comb begin
    if (!$isunknown({A,TE_B})) begin
      assert (#0 !$isunknown(Z))
        else $error("my_module: Z is X with known inputs");
    end
  end

  // TE_B high forces Z=1 immediately
  property te_forces_one;
    @(posedge TE_B) disable iff ($isunknown(TE_B))
      ##0 (Z === 1'b1);
  endproperty
  assert property (te_forces_one);

  // With TE_B low, Z tracks A on any A edge
  property track_a_when_te_low;
    @(posedge A or negedge A) disable iff ($isunknown({A,TE_B}))
      (TE_B === 1'b0) |-> ##0 (Z === A);
  endproperty
  assert property (track_a_when_te_low);

  // When TE_B drops low, Z equals A immediately
  property te_drop_tracks_a;
    @(negedge TE_B) disable iff ($isunknown(TE_B))
      ##0 (Z === A);
  endproperty
  assert property (te_drop_tracks_a);

  // Coverage
  cover property (@(posedge TE_B) ##0 (Z===1'b1));            // force path
  cover property (@(negedge TE_B) ##0 (Z===A));               // pass-through re-enable
  cover property (@(posedge A)  (TE_B===1'b0) && (Z===1'b1)); // pass-through to 1
  cover property (@(negedge A)  (TE_B===1'b0) && (Z===1'b0)); // pass-through to 0
endmodule

// Bind into DUT
bind my_module my_module_sva(.A(A), .TE_B(TE_B), .Z(Z));