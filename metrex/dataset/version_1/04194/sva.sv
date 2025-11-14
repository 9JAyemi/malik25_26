// SVA for my_module: concise, functionally complete, with key internal checks and coverage

bind my_module my_module_sva u_my_module_sva();

module my_module_sva;

  // Power-good definition
  wire power_good = (VPWR === 1'b1) && (VGND === 1'b0);
  default disable iff (!power_good);

  // Functional equivalence of X (and no-X on clean inputs)
  assert property ( (!$isunknown({A1,A2,B1,C1})) |-> ##0
                    (X === ((A1 ^ A2) & ~(B1 & C1)) && !$isunknown(X)) )
    else $error("X functional mismatch or unknown");

  // Internal gate-level consistency (guard each with relevant knowns)
  assert property ( (!$isunknown({A1,A2})) |-> ##0
                    (nand0_out_A1_A2 === ~(A1 & A2)) )
    else $error("nand0_out_A1_A2 mismatch");

  assert property ( (!$isunknown({B1,C1})) |-> ##0
                    (nand1_out_B1_C1 === ~(B1 & C1)) )
    else $error("nand1_out_B1_C1 mismatch");

  assert property ( (!$isunknown({A1,A2})) |-> ##0
                    (nand2_out_D1_or0 === (A1 | A2)) )
    else $error("or0 output mismatch");

  assert property ( (!$isunknown({nand0_out_A1_A2,nand1_out_B1_C1,nand2_out_D1_or0})) |-> ##0
                    (nand3_out_nand0_nand1 === ~(nand0_out_A1_A2 & nand1_out_B1_C1 & nand2_out_D1_or0)) )
    else $error("3-input NAND mismatch");

  // Single-input NAND acts as inverter; buffer passes through
  assert property ( (!$isunknown(nand3_out_nand0_nand1)) |-> ##0
                    (buf0_out_nand3 === ~nand3_out_nand0_nand1) )
    else $error("single-input NAND inversion mismatch");

  assert property ( ##0 (X === buf0_out_nand3) )
    else $error("BUF mismatch to X");

  // D1 has no functional effect
  assert property ( ($changed(D1) && $stable({A1,A2,B1,C1})) |-> ##0 $stable(X) )
    else $error("X changed due to D1");

  // Coverage: key functional corners and toggles
  cover property ( (A1==1'b1 && A2==1'b0 && !(B1 & C1)) ##0 (X==1'b1) );
  cover property ( (A1==1'b0 && A2==1'b1 && !(B1 & C1)) ##0 (X==1'b1) );
  cover property ( (B1 & C1) ##0 (X==1'b0) );
  cover property ( (!(A1|A2)) ##0 (X==1'b0) );
  cover property ( $rose(X) );
  cover property ( $fell(X) );

endmodule