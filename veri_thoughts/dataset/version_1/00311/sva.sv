// SVA for multiplier. Bind this to the DUT.
// Concise checks for both modes, X-prop, basic arithmetic identities, and targeted coverage.

module multiplier_sva #(
  parameter int n = 4
) (
  input  logic [n-1:0]              A,
  input  logic [n-1:0]              B,
  input  logic                      mode,
  input  logic signed [2*n-1:0]     P
);

  localparam int W  = n;
  localparam int PW = 2*n;

  // Handy min negative value for signed n-bit
  localparam logic [W-1:0] MIN_NEG = {1'b1,{(W-1){1'b0}}};

  function automatic signed [PW-1:0] sprod (input logic [W-1:0] a, b);
    sprod = $signed(a) * $signed(b);
  endfunction

  function automatic [PW-1:0] uprod (input logic [W-1:0] a, b);
    uprod = $unsigned(a) * $unsigned(b);
  endfunction

  // Core functional correctness (combinational)
  // Evaluated whenever any input changes; ignored if any input is X/Z.
  assert property (@(A or B or mode)
                   disable iff ($isunknown({A,B,mode}))
                   (mode ? (P == sprod(A,B)) : (P == uprod(A,B))))
    else $error("P mismatch with selected multiply mode");

  // No X on output when inputs known
  assert property (@(A or B or mode)
                   disable iff ($isunknown({A,B,mode}))
                   !$isunknown(P))
    else $error("P contains X/Z while inputs are known");

  // Zeroing rule: if any operand is zero, product is zero (both modes)
  assert property (@(A or B or mode)
                   disable iff ($isunknown({A,B,mode}))
                   ((A==0 || B==0) |-> (P==0)))
    else $error("0-multiply did not yield 0");

  // LSB property: product LSB equals A[0] & B[0] (both modes)
  assert property (@(A or B or mode)
                   disable iff ($isunknown({A,B,mode}))
                   (P[0] == (A[0] & B[0])))
    else $error("P[0] != A[0]&B[0]");

  // Signed-mode sign rules (for non-zero operands)
  assert property (@(A or B or mode)
                   disable iff ($isunknown({A,B,mode}))
                   (mode && (A!=0) && (B!=0) && (A[W-1]^B[W-1]) |-> P[PW-1]))
    else $error("Signed product sign should be negative");
  assert property (@(A or B or mode)
                   disable iff ($isunknown({A,B,mode}))
                   (mode && (A!=0) && (B!=0) && ~(A[W-1]^B[W-1]) |-> !P[PW-1]))
    else $error("Signed product sign should be non-negative");

  // Identity/annihilator checks
  // Unsigned mode: 1*x == x (zero-extended), x*1 == x
  assert property (@(A or B or mode)
                   disable iff ($isunknown({A,B,mode}))
                   (!mode && (A==1) |-> (P == B)))
    else $error("Unsigned 1*A identity failed (A is 1)");
  assert property (@(A or B or mode)
                   disable iff ($isunknown({A,B,mode}))
                   (!mode && (B==1) |-> (P == A)))
    else $error("Unsigned 1*B identity failed (B is 1)");
  // Signed mode: 1*x == x (sign-extended), x*1 == x
  assert property (@(A or B or mode)
                   disable iff ($isunknown({A,B,mode}))
                   (mode && (A==1) |-> (P == $signed(B))))
    else $error("Signed 1*A identity failed (A is 1)");
  assert property (@(A or B or mode)
                   disable iff ($isunknown({A,B,mode}))
                   (mode && (B==1) |-> (P == $signed(A))))
    else $error("Signed 1*B identity failed (B is 1)");

  // Targeted functional coverage
  // Exercise both modes and interesting corner cases
  cover property (@(A or B or mode) (!mode && (A==0 || B==0)));
  cover property (@(A or B or mode) (!mode && (A=={W{1'b1}}) && (B=={W{1'b1}})));
  cover property (@(A or B or mode) ( mode && ($signed(A)<0) && ($signed(B)>0)));
  cover property (@(A or B or mode) ( mode && ($signed(A)>0) && ($signed(B)<0)));
  cover property (@(A or B or mode) ( mode && ($signed(A)<0) && ($signed(B)<0)));
  cover property (@(A or B or mode) ( mode && ($signed(A)==0) && ($signed(B)!=0)));
  cover property (@(A or B or mode) ( mode && ($signed(A)==$signed(MIN_NEG)) && ($signed(B)==-1)));
  cover property (@(A or B or mode) ( mode && ($signed(A)==$signed(MIN_NEG)) && ($signed(B)==$signed(MIN_NEG))));

endmodule

// Bind into DUT
bind multiplier multiplier_sva #(.n(n)) u_multiplier_sva (
  .A(A), .B(B), .mode(mode), .P(P)
);