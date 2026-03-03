// SVA for sky130_fd_sc_lp__dfxtp (positive-edge DFF)
// Concise, high-quality checks with essential coverage.
`ifndef SKY130_FD_SC_LP__DFXTP_SVA
`define SKY130_FD_SC_LP__DFXTP_SVA

module sky130_fd_sc_lp__dfxtp_sva (
  input D, Q, CLK,
  input VPB, VPWR, VGND, VNB
);
  // Power-good definition (rails/body ties + known states)
  let pg = (VPWR === 1'b1) && (VPB === 1'b1) && (VGND === 1'b0) && (VNB === 1'b0);

  default clocking cb @(posedge CLK); endclocking

  // Functional correctness: Q holds prior-cycle D when powered
  // (avoid first-cycle $past with !$past(pg))
  assert property (disable iff (!pg || !$past(pg)) Q == $past(D));

  // Q only changes on a CLK rising edge (no glitches between clocks)
  assert property (@(posedge Q or negedge Q) disable iff (!pg) $rose(CLK));

  // Q is always 2-state (no X/Z) once powered and after first valid cycle
  assert property (disable iff (!pg || !$past(pg)) !$isunknown(Q));

  // Power pins sanity: bodies tied to rails and no X on rails
  assert property (@(posedge CLK) !$isunknown({VPWR,VPB,VGND,VNB}) && (VPWR == VPB) && (VGND == VNB));

  // Optional: clock changes are never X (sanity)
  assert property (@(posedge CLK or negedge CLK) !$isunknown(CLK));

  // Coverage: see both data values captured and both output transitions
  cover property (@(posedge CLK) pg && !$isunknown(D) && D == 1'b0);
  cover property (@(posedge CLK) pg && !$isunknown(D) && D == 1'b1);
  cover property (@(posedge CLK) pg && $past(Q) == 1'b0 && Q == 1'b1);
  cover property (@(posedge CLK) pg && $past(Q) == 1'b1 && Q == 1'b0);
endmodule

bind sky130_fd_sc_lp__dfxtp sky130_fd_sc_lp__dfxtp_sva sva_i (.*);

`endif