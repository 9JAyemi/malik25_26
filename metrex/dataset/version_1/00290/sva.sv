// SVA for multiplier. Bind this to the DUT.
// Focused, high-quality functional checks plus essential coverage.

module multiplier_sva #(parameter int N = 4)
(
  input  logic [N-1:0]       A,
  input  logic [N-1:0]       B,
  input  logic               ctrl,
  input  logic [2*N-1:0]     P
);

  // Helpers
  function automatic logic [2*N-1:0] u_mul(input logic [N-1:0] a, b);
    u_mul = $unsigned(a) * $unsigned(b);
  endfunction

  function automatic logic signed [2*N-1:0] s_mul(input logic signed [N-1:0] a, b);
    s_mul = a * b;
  endfunction

  function automatic bit neg(input logic signed [N-1:0] x);
    return x[N-1];
  endfunction

  localparam logic signed [N-1:0] S_MIN = {1'b1, {(N-1){1'b0}}};
  localparam logic signed [N-1:0] S_MAX = {1'b0, {(N-1){1'b1}}};

  // Known-ness: if inputs known, output must be known
  ap_no_x: assert property (@(*)
    (!$isunknown({A,B,ctrl})) |-> !$isunknown(P)
  );

  // Single, strong functional check (covers both modes)
  ap_functional: assert property (@(*)
    disable iff ($isunknown({A,B,ctrl}))
    P == (ctrl ? s_mul(signed'(A), signed'(B))
               : u_mul(A,B))
  );

  // Mode-specific equivalence (redundant to ap_functional, kept for clarity)
  ap_unsigned: assert property (@(*)
    disable iff ($isunknown({A,B,ctrl}))
    (ctrl==1'b0) |-> (P == u_mul(A,B))
  );

  ap_signed: assert property (@(*)
    disable iff ($isunknown({A,B,ctrl}))
    (ctrl==1'b1) |-> (P == s_mul(signed'(A), signed'(B)))
  );

  // Minimal, high-value coverage
  // Mode hits
  cp_ctrl0:  cover property (@(*)) (ctrl==1'b0);
  cp_ctrl1:  cover property (@(*)) (ctrl==1'b1);

  // Unsigned edge cases
  cp_u_zero: cover property (@(*)) (ctrl==0 && (A==0 || B==0) && P==0);
  cp_u_one:  cover property (@(*)) (ctrl==0 && (A==1 && P==B) || (B==1 && P==A));
  cp_u_max:  cover property (@(*)) (ctrl==0 && A=={N{1'b1}} && B=={N{1'b1}});

  // Unsigned one-hot multiplier (partial-product case)
  cp_u_onehotB: cover property (@(*)) (ctrl==0 && $onehot(B));
  cp_u_onehotA: cover property (@(*)) (ctrl==0 && $onehot(A));

  // Signed sign quadrants
  cp_s_pp: cover property (@(*)) (ctrl==1 && !neg(signed'(A)) && !neg(signed'(B)) && !P[2*N-1]);
  cp_s_pn: cover property (@(*)) (ctrl==1 && !neg(signed'(A)) &&  neg(signed'(B)) &&  P[2*N-1]);
  cp_s_np: cover property (@(*)) (ctrl==1 &&  neg(signed'(A)) && !neg(signed'(B)) &&  P[2*N-1]);
  cp_s_nn: cover property (@(*)) (ctrl==1 &&  neg(signed'(A)) &&  neg(signed'(B)) && !P[2*N-1]);

  // Signed extremes
  cp_s_min_x1:  cover property (@(*)) (ctrl==1 && signed'(A)==S_MIN && signed'(B)== 1);
  cp_s_min_xm1: cover property (@(*)) (ctrl==1 && signed'(A)==S_MIN && signed'(B)==-1);
  cp_s_max_xmax:cover property (@(*)) (ctrl==1 && signed'(A)==S_MAX && signed'(B)==S_MAX);

endmodule

// Bind into DUT
bind multiplier multiplier_sva #(.N(n)) multiplier_sva_i (.*);