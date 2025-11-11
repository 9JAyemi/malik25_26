// SVA checker for sky130_fd_sc_ls__a2111o
// Function: X == (A1 & A2) | B1 | C1 | D1

module sky130_fd_sc_ls__a2111o_sva (
  input logic X,
  input logic A1,
  input logic A2,
  input logic B1,
  input logic C1,
  input logic D1
);

  // 4-state functional equivalence (holds even with X/Z on inputs)
  property p_func_4state;
    @(*) X === ((A1 & A2) | B1 | C1 | D1);
  endproperty
  assert property (p_func_4state);

  // If inputs are known, output must be known
  property p_no_x_when_inputs_known;
    @(*) !$isunknown({A1,A2,B1,C1,D1}) |-> !$isunknown(X);
  endproperty
  assert property (p_no_x_when_inputs_known);

  // Targeted functional coverage (key minterms and edges)
  cover property (@(*) !A1 && !A2 && !B1 && !C1 && !D1 && (X==1'b0)); // all zero -> X=0
  cover property (@(*) !A1 && !A2 &&  B1 && !C1 && !D1 && (X==1'b1)); // B1 only
  cover property (@(*) !A1 && !A2 && !B1 &&  C1 && !D1 && (X==1'b1)); // C1 only
  cover property (@(*) !A1 && !A2 && !B1 && !C1 &&  D1 && (X==1'b1)); // D1 only
  cover property (@(*)  A1 &&  A2 && !B1 && !C1 && !D1 && (X==1'b1)); // A1&A2 only
  cover property (@(*)  A1 && !A2 && !B1 && !C1 && !D1 && (X==1'b0)); // A1 only -> X=0
  cover property (@(*) !A1 &&  A2 && !B1 && !C1 && !D1 && (X==1'b0)); // A2 only -> X=0

  // Output toggle coverage
  cover property (@(posedge X) 1'b1);
  cover property (@(negedge X) 1'b1);

endmodule

// Bind into the DUT
bind sky130_fd_sc_ls__a2111o sky130_fd_sc_ls__a2111o_sva u_sky130_fd_sc_ls__a2111o_sva (.*);