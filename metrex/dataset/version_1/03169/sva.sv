// SVA checker for multiplier
module multiplier_sva #(
  parameter int n = 4
) (
  input  logic [n-1:0]               A,
  input  logic [n-1:0]               B,
  input  logic                       mode,
  input  logic signed [2*n-1:0]      P
);

  // Handy constants
  localparam logic [n-1:0] ZERO  = '0;
  localparam logic [n-1:0] ONE   = {{n-1{1'b0}},1'b1};
  localparam logic [n-1:0] ALL1  = {n{1'b1}};
  localparam logic [n-1:0] MIN_S = ONE << (n-1);     // 1000...0
  localparam signed [n-1:0] SNEG1 = -1;

  // Functional correctness (guarded for known inputs); sample after delta to avoid glitches
  property p_func;
    @(A or B or mode)
      !$isunknown({A,B,mode})
      |-> ##0 (!$isunknown(P) &&
                P == (mode ? ($signed(A)*$signed(B)) : (A*B)));
  endproperty
  assert property (p_func);

  // Zeroing property (both modes)
  property p_zero;
    @(A or B or mode)
      (A==ZERO || B==ZERO) |-> ##0 (P=='0);
  endproperty
  assert property (p_zero);

  // Signed mode sign bit behavior for nonzero operands
  property p_signed_sign;
    @(A or B or mode)
      (!$isunknown({A,B,mode}) && mode && (A!=ZERO) && (B!=ZERO))
      |-> ##0 (P[2*n-1] == (A[n-1] ^ B[n-1]));
  endproperty
  assert property (p_signed_sign);

  // Basic knownness: when inputs known, output must be known
  property p_known_out;
    @(A or B or mode)
      !$isunknown({A,B,mode}) |-> ##0 !$isunknown(P);
  endproperty
  assert property (p_known_out);

  // Coverage: exercise both modes
  cover property (@(A or B or mode) !mode);
  cover property (@(A or B or mode)  mode);

  // Coverage: unsigned max*max
  cover property (@(A or B or mode) !mode && A==ALL1 && B==ALL1 ##0 (P==A*B));

  // Coverage: signed neg*pos => negative product
  cover property (@(A or B or mode)
                  mode && A[n-1] && !B[n-1] && A!=ZERO && B!=ZERO ##0 P[2*n-1]);

  // Coverage: signed neg*neg => positive nonzero product
  cover property (@(A or B or mode)
                  mode && A[n-1] && B[n-1] ##0 (!P[2*n-1] && P!='0));

  // Coverage: signed min * -1 corner
  cover property (@(A or B or mode)
                  mode && (A==MIN_S) && (B==ALL1) ##0 (P == ($signed(A)*$signed(B))));

  // Coverage: zero cases
  cover property (@(A or B or mode) (A==ZERO || B==ZERO) ##0 (P=='0));

endmodule

// Bind into DUT
bind multiplier multiplier_sva #(.n(n)) u_multiplier_sva (.*);