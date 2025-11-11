// SVA for sky130_fd_sc_lp__a41oi
`ifndef SKY130_FD_SC_LP__A41OI_SVA
`define SKY130_FD_SC_LP__A41OI_SVA

module sky130_fd_sc_lp__a41oi_sva (
  input logic A1, A2, A3, A4, B1,
  input logic Y,
  input logic and0_out,
  input logic nor0_out_Y
);
  // Sample on any relevant change; use ##0 to avoid delta race
  default clocking cb @(A1 or A2 or A3 or A4 or B1 or Y or and0_out or nor0_out_Y); endclocking

  // Functional equivalence (4-state)
  assert property (1 |-> ##0 (Y === ~(B1 | (A1 & A2 & A3 & A4))))
    else $error("a41oi func: Y != ~(B1 | (A1 & A2 & A3 & A4))");

  // Internal net consistency with gate intent
  assert property (1 |-> ##0 (and0_out  === (A1 & A2 & A3 & A4)))
    else $error("a41oi and0_out mismatch");
  assert property (1 |-> ##0 (nor0_out_Y === ~(B1 | and0_out)))
    else $error("a41oi nor0_out_Y mismatch");
  assert property (1 |-> ##0 (Y === nor0_out_Y))
    else $error("a41oi buf mismatch");

  // Dominance/simplifications when known
  assert property (B1 === 1'b1 |-> ##0 (Y === 1'b0))
    else $error("a41oi: B1=1 must force Y=0");
  assert property ((and0_out === 1'b1) && (B1 === 1'b0) |-> ##0 (Y === 1'b0))
    else $error("a41oi: AND=1,B1=0 must force Y=0");
  assert property ((and0_out === 1'b0) && (B1 === 1'b0) |-> ##0 (Y === 1'b1))
    else $error("a41oi: AND=0,B1=0 must force Y=1");

  // Sanity: no high-impedance
  assert property (1 |-> ##0 (Y !== 1'bz && and0_out !== 1'bz && nor0_out_Y !== 1'bz))
    else $error("a41oi: unexpected Z detected");

  // Coverage: toggles and key corners (incl. X propagation)
  cover property ($changed(A1)); cover property ($changed(A2));
  cover property ($changed(A3)); cover property ($changed(A4));
  cover property ($changed(B1)); cover property ($changed(Y));

  cover property (B1==1'b1 && Y==1'b0);
  cover property ((and0_out==1'b1) && (B1==1'b0) && (Y==1'b0));
  cover property ((and0_out==1'b0) && (B1==1'b0) && (Y==1'b1));
  cover property ($isunknown(~(B1 | (A1 & A2 & A3 & A4))) && $isunknown(Y));
endmodule

bind sky130_fd_sc_lp__a41oi sky130_fd_sc_lp__a41oi_sva sva_a41oi (.*);

`endif