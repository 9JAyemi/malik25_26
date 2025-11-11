// SVA for sky130_fd_sc_lp__invlp
module sky130_fd_sc_lp__invlp_sva (
  input logic A,
  input logic Y,
  input logic VPWR,
  input logic VGND,
  input logic VPB,
  input logic VNB
);

  // Power must remain valid whenever anything toggles
  assert property (@(posedge A or negedge A or posedge Y or negedge Y)
                   (VPWR===1 && VPB===1 && VGND===0 && VNB===0))
    else $error("invlp: power rails invalid");

  // Functional inversion on any A edge (zero-delay)
  assert property (@(posedge A or negedge A)
                   (VPWR===1 && VPB===1 && VGND===0 && VNB===0) |-> ##0 (Y === ~A))
    else $error("invlp: Y != ~A");

  // X/Z on A must propagate to Y
  assert property (@(A) $isunknown(A) |-> ##0 $isunknown(Y))
    else $error("invlp: X/Z on A did not propagate to Y");

  // Y changes only when A changes (no spurious output toggles)
  assert property (@(posedge Y or negedge Y)
                   (VPWR===1 && VPB===1 && VGND===0 && VNB===0) |-> $changed(A))
    else $error("invlp: Y changed without A changing");

  // Functional coverage
  cover property (@(A or Y) (VPWR===1 && VPB===1 && VGND===0 && VNB===0) && (A===1'b0 && Y===1'b1));
  cover property (@(A or Y) (VPWR===1 && VPB===1 && VGND===0 && VNB===0) && (A===1'b1 && Y===1'b0));
  cover property (@(posedge A));
  cover property (@(negedge A));
  cover property (@(posedge Y));
  cover property (@(negedge Y));

endmodule

bind sky130_fd_sc_lp__invlp sky130_fd_sc_lp__invlp_sva u_invlp_sva (.*);