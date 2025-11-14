// SVA for sky130_fd_sc_lp__o221ai: Y = ~((A1|A2) & (B1|B2) & C1)

bind sky130_fd_sc_lp__o221ai sky130_fd_sc_lp__o221ai_sva();

module sky130_fd_sc_lp__o221ai_sva();
  default clocking cb @(*); endclocking

  // Power rail sanity
  assert property (VPWR === 1'b1);
  assert property (VPB  === 1'b1);
  assert property (VGND === 1'b0);
  assert property (VNB  === 1'b0);

  // Internal gate correctness (when driving inputs are known)
  assert property ((!$isunknown({A1,A2})) |-> (or1_out      === (A1 | A2)));
  assert property ((!$isunknown({B1,B2})) |-> (or0_out      === (B1 | B2)));
  assert property ((!$isunknown({or1_out,or0_out,C1}))
                   |-> (nand0_out_Y === ~(or1_out & or0_out & C1)));
  assert property (Y === nand0_out_Y);

  // Functional equivalence when all inputs are known
  assert property ((!$isunknown({A1,A2,B1,B2,C1}))
                   |-> (Y === ~((A1|A2) & (B1|B2) & C1)));

  // Deterministic-X forcing cases
  assert property ((C1 == 1'b0) |-> (Y === 1'b1));
  assert property (((A1 == 1'b0) && (A2 == 1'b0)) |-> (Y === 1'b1));
  assert property (((B1 == 1'b0) && (B2 == 1'b0)) |-> (Y === 1'b1));
  assert property ((C1==1'b1 && (A1==1'b1 || A2==1'b1) && (B1==1'b1 || B2==1'b1))
                   |-> (Y === 1'b0));

  // Known-out when known-in
  assert property ((!$isunknown({A1,A2,B1,B2,C1}))
                   |-> (!$isunknown({or1_out,or0_out,nand0_out_Y,Y})));

  // Purely combinational: stable inputs imply stable output
  assert property ($stable({A1,A2,B1,B2,C1}) |-> $stable(Y));

  // Minimal coverage of key functional regions
  cover property (C1==1'b0 && Y==1'b1);
  cover property ((A1==0 && A2==0) && Y==1'b1);
  cover property ((B1==0 && B2==0) && Y==1'b1);
  cover property (C1==1'b1 && (A1||A2) && (B1||B2) && Y==1'b0);

  // Sensitization/toggle coverage
  cover property ((C1==1 && A2==0 && A1==0 && (B1||B2) && Y==1) ##1 (A1==1 && Y==0));
  cover property ((C1==1 && A1==0 && A2==0 && (B1||B2) && Y==1) ##1 (A2==1 && Y==0));
  cover property ((C1==1 && B2==0 && B1==0 && (A1||A2) && Y==1) ##1 (B1==1 && Y==0));
  cover property ((C1==1 && B1==0 && B2==0 && (A1||A2) && Y==1) ##1 (B2==1 && Y==0));
endmodule