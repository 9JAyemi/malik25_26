// SVA checker for mag_comp
module mag_comp_sva #(parameter WIDTH=4) (
  input logic               clk,
  input logic               rst_n,
  input logic [WIDTH-1:0]   A,
  input logic [WIDTH-1:0]   B,
  input logic               equal,
  input logic               greater
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  // Helper: inputs known
  function automatic bit knownAB; return !$isunknown({A,B}); endfunction

  // Core correctness: outputs exactly encode the relations
  a_rel:    assert property ( knownAB |-> ({greater, equal} == { (A > B), (A == B) }) );

  // Outputs must be known when inputs are known
  a_known:  assert property ( knownAB |-> !$isunknown({equal,greater}) );

  // Functional coverage
  c_eq:     cover property ( knownAB && (A == B) && equal  && !greater );
  c_gt:     cover property ( knownAB && (A >  B) && greater && !equal  );
  c_lt:     cover property ( knownAB && (A <  B) && !equal && !greater );

  // Extremes
  c_minmax_lt: cover property ( knownAB && (A == '0)                && (B == {WIDTH{1'b1}}) && !equal && !greater );
  c_minmax_gt: cover property ( knownAB && (A == {WIDTH{1'b1}})      && (B == '0)            && greater && !equal );

endmodule

// Bind example (connect clk/rst_n available in the bind scope)
bind mag_comp mag_comp_sva #(.WIDTH(4)) u_mag_comp_sva (
  .clk    (clk),
  .rst_n  (rst_n),
  .A      (A),
  .B      (B),
  .equal  (equal),
  .greater(greater)
);