// SVA for logic_circuit
// Checks functional equivalence, sanity, and concise full input coverage.
// Bind this module to the DUT.

module logic_circuit_sva (
  input logic a, b, c,
  input logic x, y, z
);

  // Sample on any input edge (combinational checker)
  default clocking cb @(posedge a or negedge a
                      or posedge b or negedge b
                      or posedge c or negedge c); endclocking

  // Functional equivalence
  ap_x_eq: assert property (x == a);
  ap_y_eq: assert property (y == (!a &&  b));
  ap_z_eq: assert property (z == (!a && !b && c));

  // Sanity: y and z cannot be high together; outputs known if inputs known
  ap_yz_mutex: assert property (!(y && z));
  ap_known:    assert property (!$isunknown({a,b,c}) |-> !$isunknown({x,y,z}));

  // Full input-space coverage (8 combinations)
  cp_000: cover property (!a && !b && !c);
  cp_001: cover property (!a && !b &&  c);
  cp_010: cover property (!a &&  b && !c);
  cp_011: cover property (!a &&  b &&  c);
  cp_100: cover property ( a && !b && !c);
  cp_101: cover property ( a && !b &&  c);
  cp_110: cover property ( a &&  b && !c);
  cp_111: cover property ( a &&  b &&  c);

endmodule

// Bind into the DUT (connects by name)
bind logic_circuit logic_circuit_sva sva (
  .a(a), .b(b), .c(c),
  .x(x), .y(y), .z(z)
);