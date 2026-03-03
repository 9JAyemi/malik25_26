// SVA for sky130_fd_sc_ms__or4bb
// Function: X = A | B | ~C_N | ~D_N

module sky130_fd_sc_ms__or4bb_sva (
  input logic A, B, C_N, D_N, X
);

  // Pure functional equivalence (with X/Z guard on inputs)
  always_comb
    if (!$isunknown({A,B,C_N,D_N}))
      assert (X === (A | B | ~C_N | ~D_N))
        else $error("or4bb func mismatch: X=%0b A=%0b B=%0b C_N=%0b D_N=%0b",
                    X,A,B,C_N,D_N);

  // No spurious X/Z on output when inputs are known
  assert property (!$isunknown({A,B,C_N,D_N}) |-> !$isunknown(X))
    else $error("X/XZ on output with known inputs");

  // If output is X/Z then at least one input must be X/Z
  assert property ($isunknown(X) |-> $isunknown({A,B,C_N,D_N}))
    else $error("Spurious X/Z on X without X/Z on inputs");

  // Edge-based sanity (guard unknowns)
  // Any asserting input must immediately make X=1
  assert property (disable iff ($isunknown({A,B,C_N,D_N})) @(posedge A)  X);
  assert property (disable iff ($isunknown({A,B,C_N,D_N})) @(posedge B)  X);
  assert property (disable iff ($isunknown({A,B,C_N,D_N})) @(negedge C_N) X);
  assert property (disable iff ($isunknown({A,B,C_N,D_N})) @(negedge D_N) X);

  // A deassert can only drive X low if all other terms are non-asserting
  assert property (disable iff ($isunknown({A,B,C_N,D_N}))
                   @(negedge A) (!B &&  C_N &&  D_N) |-> !X);
  assert property (disable iff ($isunknown({A,B,C_N,D_N}))
                   @(negedge B) (!A &&  C_N &&  D_N) |-> !X);
  assert property (disable iff ($isunknown({A,B,C_N,D_N}))
                   @(posedge C_N) (!A && !B &&  D_N) |-> !X);
  assert property (disable iff ($isunknown({A,B,C_N,D_N}))
                   @(posedge D_N) (!A && !B &&  C_N) |-> !X);

  // Coverage: all 16 input combinations and both X states
  logic sva_sample;
  always @(A or B or C_N or D_N) sva_sample <= ~sva_sample;

  covergroup cg_or4bb @(posedge sva_sample);
    cp_inputs: coverpoint {A,B,C_N,D_N} { bins all[] = {[0:15]}; }
    cp_X:      coverpoint X { bins low = {0}; bins high = {1}; }
  endgroup
  cg_or4bb cov = new();

  // Sanity cover: observe both functional regions
  cover property (!$isunknown({A,B,C_N,D_N}) && (X==0));
  cover property (!$isunknown({A,B,C_N,D_N}) && (X==1));

endmodule

bind sky130_fd_sc_ms__or4bb sky130_fd_sc_ms__or4bb_sva (.*);