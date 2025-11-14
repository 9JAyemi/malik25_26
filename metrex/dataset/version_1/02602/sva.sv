// SVA checker for sky130_fd_sc_lp__a311oi
// Bind this checker to the DUT instance(s).
module sky130_fd_sc_lp__a311oi_sva;

  // Power rails must be correct constants
  initial begin
    assert (VPWR === 1'b1) else $error("VPWR != 1");
    assert (VPB  === 1'b1) else $error("VPB  != 1");
    assert (VGND === 1'b0) else $error("VGND != 0");
    assert (VNB  === 1'b0) else $error("VNB  != 0");
  end

  // Combinational correctness (internal and output) and no glitches (delta-cycle checked)
  always_comb begin
    assert #0 (and0_out    === (A1 & A2 & A3))                     else $error("and0_out mismatch");
    assert #0 (nor0_out_Y  === ~(and0_out | B1 | C1))              else $error("nor0_out_Y mismatch");
    assert #0 (Y           === nor0_out_Y)                         else $error("buf mismatch");
    assert #0 (Y           === ~((A1 & A2 & A3) | B1 | C1))        else $error("Y function mismatch");
  end

  // If inputs are known, internal nodes and output must be known
  property p_no_x;
    @(A1 or A2 or A3 or B1 or C1 or Y)
      !$isunknown({A1,A2,A3,B1,C1}) |-> !$isunknown({and0_out,nor0_out_Y,Y});
  endproperty
  assert property (p_no_x);

  // Dominance/implication checks
  assert property (@(B1 or Y) (B1 === 1'b1) |-> (Y === 1'b0)) else $error("B1 dominance violated");
  assert property (@(C1 or Y) (C1 === 1'b1) |-> (Y === 1'b0)) else $error("C1 dominance violated");
  assert property (@(A1 or A2 or A3 or B1 or C1 or Y)
                   (!B1 && !C1 && (A1 & A2 & A3)) |-> (Y === 1'b0)) else $error("AND-path to 0 violated");
  assert property (@(A1 or A2 or A3 or B1 or C1 or Y)
                   (!B1 && !C1 && !(A1 & A2 & A3)) |-> (Y === 1'b1)) else $error("NOR-path to 1 violated");

  // Functional coverage: input activity and key outcome scenarios
  cover property (@(posedge A1));
  cover property (@(negedge A1));
  cover property (@(posedge A2));
  cover property (@(negedge A2));
  cover property (@(posedge A3));
  cover property (@(negedge A3));
  cover property (@(posedge B1));
  cover property (@(negedge B1));
  cover property (@(posedge C1));
  cover property (@(negedge C1));

  cover property (@(A1 or A2 or A3 or B1 or C1) (B1===1'b1) && (Y===1'b0));
  cover property (@(A1 or A2 or A3 or B1 or C1) (C1===1'b1) && (Y===1'b0));
  cover property (@(A1 or A2 or A3 or B1 or C1) (A1&&A2&&A3 && !B1 && !C1 && Y===1'b0));
  cover property (@(A1 or A2 or A3 or B1 or C1) (!A1 && !A2 && !A3 && !B1 && !C1 && Y===1'b1));

endmodule

bind sky130_fd_sc_lp__a311oi sky130_fd_sc_lp__a311oi_sva a311oi_sva_i();