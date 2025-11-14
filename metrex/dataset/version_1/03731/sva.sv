// SVA for mux4to1
module mux4to1_sva (
  input  logic [3:0] D0,
  input  logic [3:0] D1,
  input  logic [1:0] S,
  input  logic [3:0] Y
);

  function automatic logic [3:0] expY(logic [1:0] s, logic [3:0] d0, logic [3:0] d1);
    return (s == 2'b00) ? d0 :
           (s == 2'b01) ? d1 :
           (s == 2'b10) ? 4'b0100 :
                          4'b0111;
  endfunction

  // Functional equivalence (combinational correctness)
  property p_func;
    @(D0 or D1 or S or Y) 1 |-> (Y == expY(S, D0, D1));
  endproperty
  assert property (p_func)
    else $error("mux4to1 func mismatch: S=%b D0=%h D1=%h Y=%h exp=%h", S, D0, D1, Y, expY(S,D0,D1));

  // Purely combinational: output cannot change without an input change
  property p_no_latch;
    @(D0 or D1 or S or Y) $stable({D0,D1,S}) |-> $stable(Y);
  endproperty
  assert property (p_no_latch)
    else $error("mux4to1 non-comb: Y changed without input change");

  // No X/Z on Y when inputs are all known
  property p_known;
    @(D0 or D1 or S or Y) (! $isunknown({S,D0,D1})) |-> (! $isunknown(Y));
  endproperty
  assert property (p_known)
    else $error("mux4to1 X/Z on Y with known inputs: S=%b D0=%h D1=%h Y=%h", S, D0, D1, Y);

  // Functional coverage: exercise all select cases with correct Y
  cover property (@(D0 or D1 or S or Y) (S==2'b00) && (Y==D0));
  cover property (@(D0 or D1 or S or Y) (S==2'b01) && (Y==D1));
  cover property (@(D0 or D1 or S or Y) (S==2'b10) && (Y==4'b0100));
  cover property (@(D0 or D1 or S or Y) (S==2'b11) && (Y==4'b0111));

endmodule

// Bind into the DUT
bind mux4to1 mux4to1_sva i_mux4to1_sva (.D0(D0), .D1(D1), .S(S), .Y(Y));