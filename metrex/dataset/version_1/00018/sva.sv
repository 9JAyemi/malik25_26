// SVA checker for fixed_point_multiplier_adder
// Bind into DUT scope (sees DUT internals by name)
module fixed_point_multiplier_adder_sva;

  default clocking cb @(posedge CLK); endclocking

  // Helpers
  let KNOWN32(x) = !$isunknown(x);
  let KNOWN16(x) = !$isunknown(x);
  let SUM40 = ({8'h00, iG} + (iK_e << 16) + (iJ_e << 16));

  // General sanity: no X on O when inputs known
  assert property ( KNOWN16(A) && KNOWN16(B) && KNOWN16(C) && KNOWN16(D) |-> KNOWN32(O) );

  // Bypass mode correctness (note 16-bit add size → zero-extended to 32)
  assert property ( !ENABLE_DSP |-> O == {16'h0000, (iA + iC)} );

  // DSP mode composition (replicate sizing/truncation explicitly to 40b)
  assert property ( ENABLE_DSP |-> O == SUM40[31:0] );

  // Critical: dropped iF term due to 32-bit shift by 32
  assert property ( ENABLE_DSP |-> (iF << 32) == 32'd0 );
  // Cover we ever compute a nonzero iF that then gets dropped
  cover  property ( ENABLE_DSP && (iF != 32'd0) && ((iF << 32) == 32'd0) );

  // Sign-extension and split correctness
  assert property ( A_SIGNED == 0 |-> Ah[31:16] == 16'h0000 );
  assert property ( A_SIGNED == 1 |-> Ah[31:16] == {16{iA[15]}} && Ah[15:0] == iA[15:0] );
  assert property ( Bh[15:0] == iB[15:0] );
  assert property ( B_SIGNED == 0 |-> Bh[31:16] == 16'h0000 );
  assert property ( B_SIGNED == 1 |-> Bh[31:16] == {16{iB[15]}} );

  assert property ( Al[31:8] == 24'h0 && Al[7:0] == iA[7:0] );
  assert property ( Bl[31:8] == 24'h0 && Bl[7:0] == iB[7:0] );

  // Extended partials sizing (40-bit sign/zero extend as coded)
  assert property ( A_SIGNED == 0 |-> iK_e[39:24] == 16'h0000 );
  assert property ( A_SIGNED == 1 |-> iK_e[39:24] == {16{iK[31]}} );
  assert property ( B_SIGNED == 0 |-> iJ_e[39:24] == 16'h0000 );
  assert property ( B_SIGNED == 1 |-> iJ_e[39:24] == {16{iJ[31]}} );

  // Independence checks: fields that should not affect certain partials
  assert property ( $stable({iA[7:0], iB}) && $changed(iA[15:8]) |-> $stable(p_Al_Bh) );
  assert property ( $stable({iB[7:0], iA}) && $changed(iB[15:8]) |-> $stable(p_Ah_Bl) );

  // Mode-based input independence on O
  assert property ( ENABLE_DSP && $stable({A,B,A_SIGNED,B_SIGNED,ENABLE_DSP}) && $changed(C) |-> O == $past(O) );
  assert property ( ENABLE_DSP && $stable({A,B,C,A_SIGNED,B_SIGNED,ENABLE_DSP}) && $changed(D) |-> O == $past(O) );
  assert property ( !ENABLE_DSP && $stable({A,C,ENABLE_DSP}) && $changed(B) |-> O == $past(O) );
  assert property ( !ENABLE_DSP && $stable({A,C,ENABLE_DSP}) && $changed(D) |-> O == $past(O) );

  // Cover important corners
  cover property ( !ENABLE_DSP && A == 16'hFFFF && C == 16'h0001 );                    // bypass wraparound
  cover property ( ENABLE_DSP && A_SIGNED && B_SIGNED && A == 16'h8000 && B == 16'h8000 );
  cover property ( ENABLE_DSP && !A_SIGNED && !B_SIGNED && A[7:0] != 0 && B[7:0] != 0 );
  cover property ( ENABLE_DSP && $changed(D) && $stable({A,B,C}) );                    // D truly unused

endmodule

bind fixed_point_multiplier_adder fixed_point_multiplier_adder_sva;