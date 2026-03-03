// SVA for sky130_fd_sc_ls__clkdlyinv5sd1 (Y = ~A), concise and 4-state correct.
// Uses ##0 to avoid preponed-region sampling issues.

module sky130_fd_sc_ls__clkdlyinv5sd1_sva (
  input logic A,
  input logic Y
);

  // Functional equivalence (covers 0/1/X/Z via 4-state === and ~)
  property p_func_eq;
    @(A or Y) 1'b1 |-> ##0 (Y === ~A);
  endproperty
  assert property (p_func_eq)
    else $error("Y must equal bitwise NOT of A (4-state): Y=%0b A=%0b", Y, A);

  // Immediate response to A change (no latency)
  property p_resp_0delay;
    @(A) $changed(A) |-> ##0 (Y === ~A);
  endproperty
  assert property (p_resp_0delay)
    else $error("Y did not update to ~A in the same timestep after A changed");

  // No spurious Y changes without A changing
  property p_no_spurious_y;
    @(A or Y) 1'b1 |-> ##0 (!$changed(Y) || $changed(A));
  endproperty
  assert property (p_no_spurious_y)
    else $error("Y changed without a corresponding change on A");

  // Coverage: both polarities, known states, and X/Z propagation
  cover property (@(posedge A) ##0 (Y === 1'b0));
  cover property (@(negedge A) ##0 (Y === 1'b1));
  cover property (@(A or Y)   ##0 (A === 1'b0 && Y === 1'b1));
  cover property (@(A or Y)   ##0 (A === 1'b1 && Y === 1'b0));
  cover property (@(A or Y)   ##0 ($isunknown(A) && $isunknown(Y)));

endmodule

bind sky130_fd_sc_ls__clkdlyinv5sd1 sky130_fd_sc_ls__clkdlyinv5sd1_sva (.*);