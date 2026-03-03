// SVA for nor4bb: Y = ~(A | B | C_N | D_N)
module nor4bb_sva (input logic Y, A, B, C_N, D_N);

  // Sample on any input edge
  default clocking cb @ (posedge A or negedge A
                       or posedge B or negedge B
                       or posedge C_N or negedge C_N
                       or posedge D_N or negedge D_N);
  endclocking

  // Functional equivalence (4-state exact)
  assert property (Y === ~(A | B | C_N | D_N))
    else $error("nor4bb func mismatch: Y=%b A=%b B=%b C_N=%b D_N=%b",
                Y,A,B,C_N,D_N);

  // Directional sanity (only when inputs are known)
  assert property ((!$isunknown({A,B,C_N,D_N}) && (A||B||C_N||D_N)) |-> (Y === 1'b0))
    else $error("nor4bb: any input=1 must force Y=0");
  assert property ((!$isunknown({A,B,C_N,D_N}) && !(A||B||C_N||D_N)) |-> (Y === 1'b1))
    else $error("nor4bb: all inputs=0 must force Y=1");
  assert property ((!$isunknown(Y) && Y===1'b1) |-> (A===1'b0 && B===1'b0 && C_N===1'b0 && D_N===1'b0))
    else $error("nor4bb: Y=1 implies all inputs=0");
  assert property ((!$isunknown(Y) && Y===1'b0) |-> (A||B||C_N||D_N))
    else $error("nor4bb: Y=0 implies some input=1");

  // No X on Y when inputs are known
  assert property (!$isunknown({A,B,C_N,D_N}) |-> !$isunknown(Y))
    else $error("nor4bb: known inputs produced unknown Y");

  // Y changes only when some input changes
  assert property ($changed(Y) |-> ($changed(A) or $changed(B) or $changed(C_N) or $changed(D_N)))
    else $error("nor4bb: Y changed without input change");

  // Coverage: observe Y states and edges (sampled on input edges)
  cover property (Y===1'b1);
  cover property (Y===1'b0);
  cover property ($rose(Y));
  cover property ($fell(Y));

  // Full input-combination coverage (16 bins)
  covergroup cg_inputs @(cb);
    coverpoint {A,B,C_N,D_N} { bins all[] = {[4'b0000:4'b1111]}; }
  endgroup
  cg_inputs cg = new();

endmodule

// Bind into DUT
bind nor4bb nor4bb_sva nor4bb_sva_i (.Y(Y), .A(A), .B(B), .C_N(C_N), .D_N(D_N));