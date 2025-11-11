// SVA for PAD_BANK2
// Bindable checker that verifies functional intent and provides concise coverage

checker pad_bank2_chk (input logic PAD, PADIN, PADOUT, PADOEN);

  // Combinational invariants (checked continuously after settling)
  always_comb begin
    // PADIN mirrors PADOUT
    assert (PADIN === PADOUT)
      else $error("PADIN must mirror PADOUT");

    // Open-drain behavior: drive 0 only when enabled and PADOUT==0; otherwise 1
    assert (PAD === ((PADOEN && !PADOUT) ? 1'b0 : 1'b1))
      else $error("PAD incorrect for PADOEN/PADOUT");

    // No high-Z on PAD
    assert (PAD !== 1'bz)
      else $error("PAD must never be 'z'");

    // No X on outputs when inputs are known
    if (!$isunknown({PADOEN, PADOUT})) begin
      assert (!$isunknown({PAD, PADIN}))
        else $error("Outputs X with known inputs");
    end
  end

  // Bidirectional safety (both directions) for low-drive condition
  property p_low_only_when_enabled;
    (PAD === 1'b0) |-> (PADOEN && !PADOUT);
  endproperty
  assert property (p_low_only_when_enabled);

  property p_enabled_low_implies_pad_low;
    (PADOEN && !PADOUT) |-> (PAD === 1'b0);
  endproperty
  assert property (p_enabled_low_implies_pad_low);

  // Coverage: all input combinations and both PAD drive levels
  cover property (PADOEN==0 && PADOUT==0);
  cover property (PADOEN==0 && PADOUT==1);
  cover property (PADOEN==1 && PADOUT==0);
  cover property (PADOEN==1 && PADOUT==1);
  cover property (PAD==0);
  cover property (PAD==1);

endchecker

bind PAD_BANK2 pad_bank2_chk pad_bank2_chk_i (.PAD(PAD), .PADIN(PADIN), .PADOUT(PADOUT), .PADOEN(PADOEN));