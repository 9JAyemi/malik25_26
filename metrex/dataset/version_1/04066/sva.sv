// SVA checker for signed_mult. Bind this to the DUT.
// Focus: correctness of signed multiply with proper sign-extend/truncate,
// known-ness, and key corner-case coverage.

module signed_mult_sva #(
  parameter int A_WIDTH = 1,
  parameter int B_WIDTH = 1,
  parameter int P_WIDTH = 1
)(
  input  logic signed [A_WIDTH-1:0] A,
  input  logic signed [B_WIDTH-1:0] B,
  input  logic signed [P_WIDTH-1:0] P
);

  // Elaboration-time sanity
  initial begin
    if (A_WIDTH <= 0 || B_WIDTH <= 0 || P_WIDTH <= 0) begin
      $error("signed_mult_sva: illegal parameter(s): A=%0d B=%0d P=%0d", A_WIDTH, B_WIDTH, P_WIDTH);
    end
  end

  // Golden model (handles sign extend/truncate)
  function automatic signed [P_WIDTH-1:0] expP(
    input logic signed [A_WIDTH-1:0] a,
    input logic signed [B_WIDTH-1:0] b
  );
    logic signed [A_WIDTH+B_WIDTH-1:0] pr;
    logic signed [P_WIDTH-1:0]         r;
    begin
      pr = a * b;
      r  = pr;      // size-cast: sign-extend or truncate to P_WIDTH
      return r;
    end
  endfunction

  // Overflow detector (true when truncated-away bits disagree with kept sign bit)
  function automatic bit ovf(
    input logic signed [A_WIDTH-1:0] a,
    input logic signed [B_WIDTH-1:0] b
  );
    logic signed [A_WIDTH+B_WIDTH-1:0] pr;
    int hi;
    begin
      pr = a * b;
      if (P_WIDTH >= A_WIDTH+B_WIDTH) return 1'b0;
      hi = (A_WIDTH+B_WIDTH) - P_WIDTH;
      return |(pr[A_WIDTH+B_WIDTH-1:P_WIDTH] ^ {hi{pr[P_WIDTH-1]}});
    end
  endfunction

  // Core functional correctness (guarded against X/Z on inputs)
  property p_mult_correct;
    @(*) !$isunknown({A,B}) |-> (P == expP(A,B));
  endproperty
  assert property (p_mult_correct)
    else $error("P mismatch: A=%0d B=%0d P=%0d exp=%0d", A, B, P, expP(A,B));

  // If inputs are known, output must be known
  property p_known_out_when_known_in;
    @(*) !$isunknown({A,B}) |-> !$isunknown(P);
  endproperty
  assert property (p_known_out_when_known_in)
    else $error("Unknown P with known inputs: A=%b B=%b P=%b", A, B, P);

  // Zero-multiplication identity
  property p_zero_identity;
    @(*) ((A === '0) || (B === '0)) |-> (P === '0);
  endproperty
  assert property (p_zero_identity)
    else $error("Zero identity violated: A=%0d B=%0d P=%0d", A, B, P);

  // Coverage: sign combinations, zero, overflow, and extremes
  localparam logic signed [A_WIDTH-1:0] A_MIN = {1'b1, {(A_WIDTH-1){1'b0}}};
  localparam logic signed [B_WIDTH-1:0] B_MIN = {1'b1, {(B_WIDTH-1){1'b0}}};
  localparam logic signed [A_WIDTH-1:0] A_MAX = {1'b0, {(A_WIDTH-1){1'b1}}};
  localparam logic signed [B_WIDTH-1:0] B_MAX = {1'b0, {(B_WIDTH-1){1'b1}}};

  cover property (@(*) !$isunknown({A,B,P}) && (A > 0) && (B > 0) && (P > 0));
  cover property (@(*) !$isunknown({A,B,P}) && (A < 0) && (B < 0) && (P > 0));
  cover property (@(*) !$isunknown({A,B,P}) && ((A < 0) ^ (B < 0)) && (P < 0));
  cover property (@(*) !$isunknown({A,B,P}) && ((A === '0) || (B === '0)) && (P === '0));
  cover property (@(*) !$isunknown({A,B,P}) && ovf(A,B));
  cover property (@(*) !$isunknown({A,B,P}) && (A == A_MIN));
  cover property (@(*) !$isunknown({A,B,P}) && (B == B_MIN));
  cover property (@(*) !$isunknown({A,B,P}) && (A == A_MAX));
  cover property (@(*) !$isunknown({A,B,P}) && (B == B_MAX));

endmodule

// Bind into the DUT
bind signed_mult signed_mult_sva #(
  .A_WIDTH(A_WIDTH),
  .B_WIDTH(B_WIDTH),
  .P_WIDTH(P_WIDTH)
) signed_mult_sva_i (
  .A(A),
  .B(B),
  .P(P)
);