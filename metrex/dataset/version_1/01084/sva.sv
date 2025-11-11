// SVA bind module for multiplier. Focused, concise, and parameter-agnostic.
module multiplier_asserts #(parameter int N = 8)
(
  input  logic [N-1:0] A,
  input  logic [N-1:0] B,
  input  logic         mode,
  input  logic [N-1:0] P
);

  // Helpers
  function automatic logic [N-1:0] u_ref(input logic [N-1:0] a, b);
    u_ref = ($unsigned(a) * $unsigned(b))[N-1:0];
  endfunction

  function automatic logic [N-1:0] s_ref(input logic [N-1:0] a, b);
    logic signed [N-1:0] sa = a, sb = b;
    logic signed [2*N-1:0] prod = sa * sb;
    s_ref = prod[N-1:0];
  endfunction

  function automatic bit has_pair_01(input logic [N-1:0] b);
    logic [N:0] x; x = {b[N-1], b};
    return |((~x[N:1]) & x[N-1:0]);
  endfunction

  function automatic bit has_pair_10(input logic [N-1:0] b);
    logic [N:0] x; x = {b[N-1], b};
    return |(x[N:1] & ~x[N-1:0]);
  endfunction

  // Core functional correctness (unsigned and signed)
  assert property (@(A or B or mode)
    (!$isunknown({A,B,mode}) && (mode==1'b0)) |-> P == u_ref(A,B))
    else $error("Unsigned multiply mismatch: P=%0h A=%0h B=%0h", P, A, B);

  assert property (@(A or B or mode)
    (!$isunknown({A,B,mode}) && (mode==1'b1)) |-> P == s_ref(A,B))
    else $error("Signed multiply mismatch: P=%0h A=%0h B=%0h", P, A, B);

  // No-X on output when inputs are known
  assert property (@(A or B or mode)
    (!$isunknown({A,B,mode})) |-> !$isunknown(P))
    else $error("P has X/Z with known inputs");

  // Sanity identities
  assert property (@(A or B or mode)
    (!$isunknown({A,B,mode}) && ((A=='0) || (B=='0))) |-> (P=='0))
    else $error("Zero multiplicand should yield zero");

  assert property (@(A or B or mode)
    (!$isunknown({A,B,mode}) && (B == {{(N-1){1'b0}},1'b1})) |-> (P == A))
    else $error("Multiply by 1 failed");

  assert property (@(A or B or mode)
    (!$isunknown({A,B,mode}) && mode && ($signed(B) == -1)) |-> (P == (-$signed(A))[N-1:0]))
    else $error("Multiply by -1 (signed) failed");

  // Output changes only when inputs change (no glitches relative to input activity)
  assert property (@(P) !$isunknown(P) |-> $changed({A,B,mode}))
    else $error("P changed without input change");

  // Functional coverage (modes, corners, Booth-like adjacent bit patterns)
  cover property (@(A or B or mode) (! $isunknown({A,B,mode}) && (mode==0)));
  cover property (@(A or B or mode) (! $isunknown({A,B,mode}) && (mode==1)));

  cover property (@(A or B or mode) (! $isunknown({A,B,mode}) && (A=='0)));
  cover property (@(A or B or mode) (! $isunknown({A,B,mode}) && (B=='0)));
  cover property (@(A or B or mode) (! $isunknown({A,B,mode}) && (A=={N{1'b1}})));
  cover property (@(A or B or mode) (! $isunknown({A,B,mode}) && (B=={N{1'b1}})));

  // Signed-mode sign combinations
  cover property (@(A or B or mode) (! $isunknown({A,B,mode}) && mode && ($signed(A)<0)  && ($signed(B)>=0)));
  cover property (@(A or B or mode) (! $isunknown({A,B,mode}) && mode && ($signed(A)>=0) && ($signed(B)<0)));
  cover property (@(A or B or mode) (! $isunknown({A,B,mode}) && mode && ($signed(A)<0)  && ($signed(B)<0)));

  // Adjacent bit patterns in {B[n-1],B} to exercise 01/10 Booth decisions
  cover property (@(A or B or mode) has_pair_01(B));
  cover property (@(A or B or mode) has_pair_10(B));

endmodule

// Bind to DUT; parameter N inferred from port width
bind multiplier multiplier_asserts #(.N($bits(A))) u_multiplier_asserts (.A(A), .B(B), .mode(mode), .P(P));