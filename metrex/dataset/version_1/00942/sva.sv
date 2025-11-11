// SVA for sky130_fd_sc_hd__o221ai
// Function: Y = ~((A1 | A2) & (B1 | B2) & C1)

module sky130_fd_sc_hd__o221ai_sva (
  input logic A1, A2, B1, B2, C1, Y,
  input logic or0_out, or1_out, nand0_out_Y,
  input logic VPWR, VGND, VPB, VNB
);

  // Local reductions
  logic G1, G2, supplies_ok, inputs_known;
  assign G1 = (A1 | A2);
  assign G2 = (B1 | B2);
  assign supplies_ok  = (VPWR===1'b1 && VPB===1'b1 && VGND===1'b0 && VNB===1'b0);
  assign inputs_known = !$isunknown({A1,A2,B1,B2,C1});

  // Supplies must never change
  assert property (@(posedge VPWR or negedge VPWR) 0);
  assert property (@(posedge VPB  or negedge VPB ) 0);
  assert property (@(posedge VGND or negedge VGND) 0);
  assert property (@(posedge VNB  or negedge VNB ) 0);

  // Combinational functional correctness (and internal net equivalences) in same delta
  property p_func;
    @(A1 or A2 or B1 or B2 or C1 or or0_out or or1_out or nand0_out_Y or Y)
      disable iff (!supplies_ok || !inputs_known)
      1'b1 |-> ##0 (
        (or1_out     === G1)                           &&
        (or0_out     === G2)                           &&
        (nand0_out_Y === ~(G1 & G2 & C1))              &&
        (Y           === nand0_out_Y)                  &&
        (Y           === ~(G1 & G2 & C1))
      );
  endproperty
  assert property (p_func);

  // Necessary/sufficient conditions for Y low/high
  assert property (@(A1 or A2 or B1 or B2 or C1)
                   disable iff (!supplies_ok || !inputs_known)
                   (G1 && G2 && C1) |-> ##0 (Y==1'b0));
  assert property (@(A1 or A2 or B1 or B2 or C1)
                   disable iff (!supplies_ok || !inputs_known)
                   (Y==1'b0) |-> ##0 (G1 && G2 && C1));
  assert property (@(A1 or A2 or B1 or B2 or C1)
                   disable iff (!supplies_ok || !inputs_known)
                   (!G1 || !G2 || !C1) |-> ##0 (Y==1'b1));

  // Coverage: all 8 functional input-group combinations, and both Y edges
  genvar g1, g2, c;
  generate
    for (g1=0; g1<2; g1++) begin : cov_g1
      for (g2=0; g2<2; g2++) begin : cov_g2
        for (c=0; c<2; c++) begin : cov_c
          cover property (@(A1 or A2 or B1 or B2 or C1)
                          disable iff (!supplies_ok || !inputs_known)
                          ##0 (G1==g1 && G2==g2 && C1==c));
        end
      end
    end
  endgenerate
  cover property (@(A1 or A2 or B1 or B2 or C1)
                  disable iff (!supplies_ok || !inputs_known) $rose(Y));
  cover property (@(A1 or A2 or B1 or B2 or C1)
                  disable iff (!supplies_ok || !inputs_known) $fell(Y));

endmodule

// Bind into the DUT
bind sky130_fd_sc_hd__o221ai sky130_fd_sc_hd__o221ai_sva u_o221ai_sva (
  .A1(A1), .A2(A2), .B1(B1), .B2(B2), .C1(C1), .Y(Y),
  .or0_out(or0_out), .or1_out(or1_out), .nand0_out_Y(nand0_out_Y),
  .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB)
);