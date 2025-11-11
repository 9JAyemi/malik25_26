// SVA for sky130_fd_sc_hvl__o22a: X = (A1 | A2) & (B1 | B2)
// Bind inside the DUT so we can check internal nets.
module o22a_sva;

  // Functional correctness after inputs settle (end of timestep)
  assert property (@(posedge A1 or negedge A1 or
                     posedge A2 or negedge A2 or
                     posedge B1 or negedge B1 or
                     posedge B2 or negedge B2)
                   ##0 (X === ((A1 | A2) & (B1 | B2))))
    else $error("o22a func mismatch: X=%b A1=%b A2=%b B1=%b B2=%b", X,A1,A2,B1,B2);

  // Gate-by-gate internal consistency
  assert property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2)
                   ##0 (or0_out === (A1 | A2)))
    else $error("or0_out mismatch");
  assert property (@(posedge B1 or negedge B1 or posedge B2 or negedge B2)
                   ##0 (or1_out === (B1 | B2)))
    else $error("or1_out mismatch");
  assert property (@(posedge or0_out or negedge or0_out or
                     posedge or1_out or negedge or1_out)
                   ##0 (and0_out_X === (or0_out & or1_out)))
    else $error("and0_out_X mismatch");
  assert property (@(posedge and0_out_X or negedge and0_out_X)
                   ##0 (X === and0_out_X))
    else $error("buf/X mismatch");

  // No X/Z on internal/output when inputs are all known
  assert property (@(posedge A1 or negedge A1 or
                     posedge A2 or negedge A2 or
                     posedge B1 or negedge B1 or
                     posedge B2 or negedge B2)
                   (!$isunknown({A1,A2,B1,B2})) |-> ##0 (!$isunknown({or0_out,or1_out,and0_out_X,X})))
    else $error("Unknown detected with known inputs");

  // Compact functional coverage
  // X edges
  cover property (@(posedge X));
  cover property (@(negedge X));

  // All four single-input activations to achieve X==1
  cover property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or
                    posedge B1 or negedge B1 or posedge B2 or negedge B2)
                  ##0 (A1 && !A2 && B1 && !B2 && X));
  cover property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or
                    posedge B1 or negedge B1 or posedge B2 or negedge B2)
                  ##0 (A1 && !A2 && !B1 && B2 && X));
  cover property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or
                    posedge B1 or negedge B1 or posedge B2 or negedge B2)
                  ##0 (!A1 && A2 && B1 && !B2 && X));
  cover property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or
                    posedge B1 or negedge B1 or posedge B2 or negedge B2)
                  ##0 (!A1 && A2 && !B1 && B2 && X));

  // Representative X==0 cases
  cover property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or
                    posedge B1 or negedge B1 or posedge B2 or negedge B2)
                  ##0 (!A1 && !A2 && (B1||B2) && !X));
  cover property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or
                    posedge B1 or negedge B1 or posedge B2 or negedge B2)
                  ##0 ((A1||A2) && !B1 && !B2 && !X));
  cover property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or
                    posedge B1 or negedge B1 or posedge B2 or negedge B2)
                  ##0 (!A1 && !A2 && !B1 && !B2 && !X));

endmodule

bind sky130_fd_sc_hvl__o22a o22a_sva o22a_sva_i();