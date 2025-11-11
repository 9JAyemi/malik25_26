// SVA bind module for sky130_fd_sc_ms__clkinv
module sky130_fd_sc_ms__clkinv_sva (input logic A, Y);

  // Functional equivalence (4-state)
  always_comb
    assert (Y === ~A)
      else $error("clkinv: Y != ~A (4-state)");

  // Immediate, opposite update on any A toggle
  assert property (@(posedge A or negedge A) ##0 (Y === ~A))
    else $error("clkinv: propagation mismatch at A edge");

  // Y must not change unless A changes
  assert property (@(posedge Y or negedge Y) $changed(A))
    else $error("clkinv: Y changed without A change");

  // Known A must yield known, correct Y
  assert property (@(posedge A or negedge A or posedge Y or negedge Y)
                   (!$isunknown(A)) |-> (!$isunknown(Y) && (Y === ~A)))
    else $error("clkinv: known A did not produce known inverted Y");

  // Unknown A must propagate to unknown Y
  assert property (@(posedge A or negedge A) $isunknown(A) |-> $isunknown(Y))
    else $error("clkinv: unknown A did not propagate to Y");

  // Directional edge checks
  assert property (@(posedge A) $fell(Y))
    else $error("clkinv: Y did not fall on A rise");
  assert property (@(negedge A) $rose(Y))
    else $error("clkinv: Y did not rise on A fall");

  // Coverage: values, transitions, and X-propagation
  cover property (@(posedge A) (A==1'b1 && Y==1'b0));
  cover property (@(negedge A) (A==1'b0 && Y==1'b1));
  cover property (@(posedge A or negedge A) !$isunknown(A) && !$isunknown(Y));
  cover property (@(posedge A or negedge A)  $isunknown(A) &&  $isunknown(Y));
  cover property (@(posedge Y));
  cover property (@(negedge Y));

endmodule

bind sky130_fd_sc_ms__clkinv sky130_fd_sc_ms__clkinv_sva u_clkinv_sva (.A(A), .Y(Y));