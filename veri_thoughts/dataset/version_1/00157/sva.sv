// SVA for sky130_fd_sc_ms__mux_2_1
// Bind these assertions to the DUT

module sky130_fd_sc_ms__mux_2_1_sva (
  input out,
  input in0,
  input in1,
  input sel,
  input VPWR,
  input VGND,
  input VPB,
  input VNB
);
  wire rails_known = !$isunknown({VPWR,VGND,VPB,VNB});
  wire pwr_ok = rails_known && VPWR && VPB && !VGND && !VNB;

  // Functional correctness on any relevant change
  assert property (@(in0 or in1 or sel or VPWR or VGND or VPB or VNB)
                   pwr_ok |-> ##0 (out === (sel ? in1 : in0)));

  // Out has no X when powered and inputs known
  assert property (@(in0 or in1 or sel or VPWR or VGND or VPB or VNB)
                   pwr_ok && !$isunknown({in0,in1,sel}) |-> ##0 !$isunknown(out));

  // Follow selected data on change
  assert property (@(in0 or sel or VPWR or VGND or VPB or VNB)
                   pwr_ok && (sel==1'b0) && $changed(in0) |-> ##0 (out===in0));
  assert property (@(in1 or sel or VPWR or VGND or VPB or VNB)
                   pwr_ok && (sel==1'b1) && $changed(in1) |-> ##0 (out===in1));

  // No spurious change from unselected input
  assert property (@(in1 or sel) pwr_ok && (sel==1'b0) && $changed(in1) |-> ##0 !$changed(out));
  assert property (@(in0 or sel) pwr_ok && (sel==1'b1) && $changed(in0) |-> ##0 !$changed(out));

  // On sel change, out equals newly selected input
  assert property (@(sel or in0 or in1 or VPWR or VGND or VPB or VNB)
                   pwr_ok && $changed(sel) |-> ##0 (out === (sel ? in1 : in0)));

  // When inputs equal, out equals them regardless of sel
  assert property (@(in0 or in1 or sel or VPWR or VGND or VPB or VNB)
                   pwr_ok && (in0===in1) |-> ##0 (out===in0));

  // Bias pins tied correctly to rails when known
  assert property (@(VPWR or VGND or VPB or VNB)
                   rails_known |-> (VPB===VPWR && VNB===VGND));

  // Coverage
  cover property (@(VPWR or VGND or VPB or VNB) (!$past(pwr_ok,1,1'b0)) && pwr_ok); // power good observed
  cover property (@(in0 or in1 or sel or VPWR or VGND or VPB or VNB) pwr_ok && sel==1'b0);
  cover property (@(in0 or in1 or sel or VPWR or VGND or VPB or VNB) pwr_ok && sel==1'b1);
  cover property (@(sel) pwr_ok && $changed(sel));
  cover property (@(in0) pwr_ok && (sel==1'b0) && $changed(in0));
  cover property (@(in1) pwr_ok && (sel==1'b1) && $changed(in1));
  cover property (@(in0 or in1 or sel) pwr_ok && (in0!==in1) && $changed(sel) && $changed(out));
endmodule

bind sky130_fd_sc_ms__mux_2_1 sky130_fd_sc_ms__mux_2_1_sva (.*);