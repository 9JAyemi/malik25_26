// SVA checker for multiplier
module multiplier_sva #(parameter int n = 8) (
  input  logic [n-1:0]       A,
  input  logic [n-1:0]       B,
  input  logic               ctrl,
  input  logic [2*n-1:0]     P
);

  // A simple sampling clock for concurrent SVA
  default clocking cb @(posedge $global_clock); endclocking

  // 2n-bit extensions and expected results
  logic [2*n-1:0] uA, uB, sA, sB;
  logic [2*n-1:0] exp_u, exp_s;

  assign uA   = {{n{1'b0}},       A};
  assign uB   = {{n{1'b0}},       B};
  assign sA   = {{n{A[n-1]}},     A};
  assign sB   = {{n{B[n-1]}},     B};
  assign exp_u = uA * uB;
  assign exp_s = $signed(sA) * $signed(sB);

  // No X/Z on output when inputs are known
  assert property (!$isunknown({A,B,ctrl}) |-> !$isunknown(P))
    else $error("P has X/Z with known inputs");

  // Correctness: unsigned mode
  assert property (disable iff ($isunknown({A,B,ctrl,P})))
    (ctrl==1'b0) |-> (P == exp_u)
    else $error("Unsigned multiply mismatch");

  // Correctness: signed (two's complement) mode
  assert property (disable iff ($isunknown({A,B,ctrl,P})))
    (ctrl==1'b1) |-> (P == exp_s)
    else $error("Signed multiply mismatch");

  // Zero-multiplicand rule (both modes)
  assert property (disable iff ($isunknown({A,B,ctrl,P})))
    ((A=={n{1'b0}}) || (B=={n{1'b0}})) |-> (P=={2*n{1'b0}})
    else $error("Zero multiplicand must yield zero product");

  // LSB property (both modes): P[0] == A[0] & B[0]
  assert property (disable iff ($isunknown({A,B})))
    (P[0] == (A[0] & B[0]))
    else $error("LSB of product incorrect");

  // Signed mode sign-bit consistency (no overflow in 2n-bit): either product is zero or sign matches XOR
  assert property (disable iff ($isunknown({A,B,ctrl,P})))
    (ctrl) |-> ( (P == {2*n{1'b0}}) || (P[2*n-1] == (A[n-1] ^ B[n-1])) )
    else $error("Signed product sign-bit incorrect");

  // Basic functional coverage
  cover property (ctrl==0 && A!=0 && B!=0 && P==exp_u);
  cover property (ctrl==1 && A!=0 && B!=0 && P==exp_s);

  // Mode coverage
  cover property (ctrl==0);
  cover property (ctrl==1);

  // Signed mode operand sign combinations
  cover property (ctrl && (A[n-1]==0) && (B[n-1]==0)); // + * +
  cover property (ctrl && (A[n-1]==1) && (B[n-1]==0)); // - * +
  cover property (ctrl && (A[n-1]==0) && (B[n-1]==1)); // + * -
  cover property (ctrl && (A[n-1]==1) && (B[n-1]==1)); // - * -

  // Extremes in signed mode
  localparam logic [n-1:0] MIN_NEG = {1'b1, {(n-1){1'b0}}};
  localparam logic [n-1:0] NEG_ONE = {n{1'b1}};
  cover property (ctrl && (A==MIN_NEG));
  cover property (ctrl && (B==MIN_NEG));
  cover property (ctrl && (A==NEG_ONE));
  cover property (ctrl && (B==NEG_ONE));

  // Exercise Booth-like boundary patterns in B (01 and 10) under signed mode
  genvar i;
  generate
    for (i=0; i<n-1; i++) begin : cov_booth_patterns
      cover property (ctrl && ( B[i] && !B[i+1] ));
      cover property (ctrl && (!B[i] &&  B[i+1] ));
    end
  endgenerate

endmodule

// Bind the checker to the DUT
bind multiplier multiplier_sva #(.n(n)) u_multiplier_sva (.*);