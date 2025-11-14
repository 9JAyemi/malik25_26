// SVA for my_inverter
module my_inverter_sva (input logic A, Y);

  // Functional correctness (handles 4-state): Y must always be bitwise NOT of A
  property inv_func_correct;
    @(A or Y) 1 |-> ##0 (Y === ~A);
  endproperty
  assert property (inv_func_correct)
    else $error("my_inverter SVA: Y != ~A");

  // Y should never be high‑Z
  property y_never_z;
    @(Y) 1 |-> ##0 (Y !== 1'bz);
  endproperty
  assert property (y_never_z)
    else $error("my_inverter SVA: Y is Z");

  // Coverage: known values and transitions
  cover property (@(A) (A === 1'b0) ##0 (Y === 1'b1));
  cover property (@(A) (A === 1'b1) ##0 (Y === 1'b0));
  cover property (@(posedge A) ##0 (Y === 1'b0));
  cover property (@(negedge A) ##0 (Y === 1'b1));

  // Coverage: unknown driving
  cover property (@(A) (A === 1'bx) ##0 (Y === 1'bx));
  cover property (@(A) (A === 1'bz) ##0 (Y === 1'bx));

endmodule

// Bind into DUT
bind my_inverter my_inverter_sva u_my_inverter_sva (.A(A), .Y(Y));