// SVA checker for inputiso1n
// Bind into the DUT to access internal nets (A_iso, SLEEP_B_iso, ...).
module inputiso1n_sva;

  // Power-good when all rails asserted high
  wire power_good = (VPWR===1'b1) && (VGND===1'b1) && (VPB===1'b1) && (VNB===1'b1);

  // Combinational assertions
  always_comb begin
    // Internal net equivalences
    assert #0 (A_iso        === (A ^ VPWR))        else $error("A_iso mismatch");
    assert #0 (SLEEP_B_iso  === (SLEEP_B ^ VGND))  else $error("SLEEP_B_iso mismatch");
    assert #0 (VPWR_iso     === VPWR)              else $error("VPWR_iso mismatch");
    assert #0 (VGND_iso     === VGND)              else $error("VGND_iso mismatch");
    assert #0 (VPB_iso      === VPB)               else $error("VPB_iso mismatch");
    assert #0 (VNB_iso      === VNB)               else $error("VNB_iso mismatch");

    // Exact Boolean function for X
    assert #0 (X === ((A ^ VPWR) & (SLEEP_B ^ VGND) & VPWR & VGND & VPB & VNB))
      else $error("X function mismatch");

    // If any rail is 0, X must be 0 (due to the AND with rails)
    assert #0 ( (VPWR===1 && VGND===1 && VPB===1 && VNB===1) || (X===1'b0) )
      else $error("X not low when any rail is low");

    // When power good, behavior simplifies to X == (~A & ~SLEEP_B)
    assert #0 ( !power_good || (X === ((~A) & (~SLEEP_B))) )
      else $error("X not ~A & ~SLEEP_B under power_good");

    // If all inputs are known, X must be known
    assert #0 ( $isunknown({A,SLEEP_B,VPWR,VGND,VPB,VNB}) || !$isunknown(X) )
      else $error("X unknown while inputs are known");
  end

  // Minimal yet meaningful functional coverage
  always_comb begin
    cover (X===1'b1);                                                    // X can assert
    cover (power_good && (A===1'b0) && (SLEEP_B===1'b0) && (X===1'b1));  // pass-through case under rails-high
    cover (power_good && (SLEEP_B===1'b1) && (X===1'b0));                // clamp via SLEEP_B under rails-high
    cover (!power_good && (X===1'b0));                                   // any rail low forces X low
  end

endmodule

// Bind the checker into every instance of inputiso1n
bind inputiso1n inputiso1n_sva sva();