// SVA for sky130_fd_sc_hvl__einvp (enabled inverter with tri-state output)
module sky130_fd_sc_hvl__einvp_sva (input logic Z, A, TE);

  // Functional correctness
  // TE=0 => tri-state
  assert property (TE === 1'b0 |-> Z === 1'bz)
    else $error("einvp: TE=0 must tri-state Z");

  // TE=1 and A known => Z == ~A and not Z
  assert property (TE === 1'b1 && !$isunknown(A) |-> (Z === ~A && Z !== 1'bz))
    else $error("einvp: TE=1, Z must be ~A and not Z");

  // X-propagation
  assert property (TE === 1'b1 && $isunknown(A) |-> $isunknown(Z))
    else $error("einvp: TE=1 with A unknown must make Z unknown");

  assert property ($isunknown(TE) |-> $isunknown(Z))
    else $error("einvp: Unknown TE must make Z unknown");

  // Only drive when enabled
  assert property ((Z === 1'b0 || Z === 1'b1) |-> TE === 1'b1)
    else $error("einvp: Z driven while TE!=1");

  // Power rails (available as supplies in DUT scope)
  assert property (VPWR === 1'b1 && VPB === 1'b1 && VGND === 1'b0 && VNB === 1'b0)
    else $error("einvp: Power rails not at expected constants");

  // Minimal functional coverage
  cover property (TE === 1'b0 && Z === 1'bz);
  cover property (TE === 1'b1 && A === 1'b0 && Z === 1'b1);
  cover property (TE === 1'b1 && A === 1'b1 && Z === 1'b0);
  cover property (TE === 1'b1 && A === 1'b0 ##1 A === 1'b1 && Z === 1'b0);
  cover property (TE === 1'b1 && A === 1'b1 ##1 A === 1'b0 && Z === 1'b1);
  cover property (TE === 1'b0 ##1 TE === 1'b1 ##1 TE === 1'b0);

endmodule

bind sky130_fd_sc_hvl__einvp sky130_fd_sc_hvl__einvp_sva u_einvp_sva (.*);