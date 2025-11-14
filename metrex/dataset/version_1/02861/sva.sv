// SVA checker and bind for sky130_fd_sc_ls__or2b
// Function: X == (A | ~B_N)

module sky130_fd_sc_ls__or2b_sva (
  input logic A,
  input logic B_N,
  input logic X,
  input logic not0_out,
  input logic or0_out_X
);

  // Combinational functional/structural equivalence (4-state clean)
  always_comb begin
    assert (X === (A | ~B_N)) else $error("X != (A | ~B_N)");
    assert (not0_out === ~B_N) else $error("not0_out != ~B_N");
    assert (or0_out_X === (not0_out | A)) else $error("or0_out_X != (not0_out | A)");
    assert (X === or0_out_X) else $error("X != or0_out_X");
  end

  // No X on output when inputs are known
  property no_x_out_when_inputs_known;
    @(A or B_N) (! $isunknown({A,B_N})) |-> (! $isunknown(X));
  endproperty
  assert property (no_x_out_when_inputs_known);

  // Edge-cause effects
  assert property (@(posedge A) X);                // A rising forces X=1
  assert property (@(negedge B_N) X);              // B_N falling forces X=1
  assert property (@(negedge A)  B_N |-> !X);      // If B_N=1 and A falls, X=0
  assert property (@(posedge B_N) !A  |-> !X);     // If A=0 and B_N rises, X=0

  // Functional coverage of input space
  cover property (@(A or B_N) (A==0 && B_N==0));
  cover property (@(A or B_N) (A==0 && B_N==1));
  cover property (@(A or B_N) (A==1 && B_N==0));
  cover property (@(A or B_N) (A==1 && B_N==1));

  // Coverage of key output-driving edges
  cover property (@(posedge A) X);
  cover property (@(negedge B_N) X);
  cover property (@(negedge A)  B_N && !X);
  cover property (@(posedge B_N) !A  && !X);

endmodule

// Bind into DUT (binds to internal nets by name)
bind sky130_fd_sc_ls__or2b sky130_fd_sc_ls__or2b_sva u_or2b_sva (.*);