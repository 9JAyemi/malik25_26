// SVA checker for sky130_fd_sc_hd__clkinv
// Concise, quality-focused assertions and coverage.
// Bind this to the DUT instance.

module clkinv_sva(input logic A, input logic Y);

  // Functional correctness (handle delta cycles with ##0)
  // If A is known, Y must be bitwise invert of A in the same time (next delta).
  assert property (@(A or Y) (A === 1'b0 || A === 1'b1) |-> ##0 (Y === ~A))
    else $error("clkinv: Y must be ~A when A is known");

  // X/Z propagation: if A is unknown, Y must be unknown (not 0/1).
  assert property (@(A or Y) $isunknown(A) |-> ##0 $isunknown(Y))
    else $error("clkinv: Unknown A must propagate to Y");

  // No loss of uncertainty: if Y is known, A must be known.
  assert property (@(A or Y) !$isunknown(Y) |-> ##0 !$isunknown(A))
    else $error("clkinv: Known Y implies known A");

  // Y must never be high-Z
  assert property (@(A or Y) ##0 !(Y === 1'bz))
    else $error("clkinv: Y must never be Z");

  // Lightweight functional coverage
  cover property (@(A or Y) (A===1'b0) ##0 (Y===1'b1));
  cover property (@(A or Y) (A===1'b1) ##0 (Y===1'b0));
  cover property (@(A or Y) $isunknown(A) ##0 $isunknown(Y));

endmodule

// Bind into the DUT
bind sky130_fd_sc_hd__clkinv clkinv_sva u_clkinv_sva (.A(A), .Y(Y));