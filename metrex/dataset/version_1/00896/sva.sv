// SVA checker for sky130_fd_sc_ls__a211o
// Bind into the DUT; no DUT edits required.

`ifndef SKY130_FD_SC_LS__A211O_SVA
`define SKY130_FD_SC_LS__A211O_SVA

module sky130_fd_sc_ls__a211o_sva;

  // Sample on any relevant signal change (inputs, output, internals)
  default clocking cb @ (A1 or A2 or B1 or C1 or X or and0_out or or0_out_X); endclocking

  // Functional equivalence
  assert property (X == ((A1 & A2) | B1 | C1));

  // Internal gate consistency
  assert property (and0_out   == (A1 & A2));
  assert property (or0_out_X  == (and0_out | B1 | C1));
  assert property (X          == or0_out_X);

  // Dominance and reduction checks
  assert property ((B1 || C1) |-> X);
  assert property ((!B1 && !C1) |-> (X == (A1 & A2)));

  // No X/Z on any relevant net
  assert property (!$isunknown({A1, A2, B1, C1, X, and0_out, or0_out_X}));

  // Output changes must be caused by an input change
  property x_change_has_cause;
    @(posedge X or negedge X) $changed(A1) || $changed(A2) || $changed(B1) || $changed(C1);
  endproperty
  assert property (x_change_has_cause);

  // Coverage: exercise key functional regions and toggles
  cover property ((!B1 && !C1 && !A1 && !A2) && (X==0));
  cover property ((!B1 && !C1 && !A1 &&  A2) && (X==0));
  cover property ((!B1 && !C1 &&  A1 && !A2) && (X==0));
  cover property ((!B1 && !C1 &&  A1 &&  A2) && (X==1));
  cover property (( B1 && !C1) && (X==1));
  cover property ((!B1 &&  C1) && (X==1));
  cover property (( B1 &&  C1) && (X==1));
  cover property ($rose(X));
  cover property ($fell(X));

endmodule

bind sky130_fd_sc_ls__a211o sky130_fd_sc_ls__a211o_sva sva_i();

`endif