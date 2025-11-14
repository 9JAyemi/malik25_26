// SVA checkers for ripple_carry_adder and full_adder

// Checker for the 4-bit ripple-carry adder
module rca_sva (
  input logic [3:0] A,
  input logic [3:0] B,
  input logic       CIN,
  input logic [3:0] SUM,
  input logic       COUT
);
  // Sample on any change of inputs/outputs (delta-safe)
  event ev;
  always @* if ($changed({A,B,CIN,SUM,COUT})) -> ev;

  // Compute expected carry chain and sum
  logic [3:0] p, g;
  logic c0, c1, c2, c3, co;
  logic [3:0] sum_exp;

  assign p       = A ^ B;
  assign g       = A & B;
  assign c0      = CIN;
  assign c1      = g[0] | (p[0] & c0);
  assign c2      = g[1] | (p[1] & c1);
  assign c3      = g[2] | (p[2] & c2);
  assign co      = g[3] | (p[3] & c3);
  assign sum_exp = p ^ {c3, c2, c1, c0};

  // X/Z checks
  assert property (@(ev) !$isunknown({A,B,CIN,SUM,COUT}))
    else $error("X/Z detected on ports");

  // Functional correctness (end-to-end)
  assert property (@(ev) {COUT, SUM} == A + B + CIN)
    else $error("Adder result mismatch");

  // Bit/carry-level correctness (will flag the MSB carry-out bug if present)
  assert property (@(ev) SUM  == sum_exp)
    else $error("SUM bits mismatch");
  assert property (@(ev) COUT == co)
    else $error("COUT mismatch (MSB carry-out)");

  // Useful coverage
  // Full propagate chain with CIN ripple to COUT
  cover property (@(ev) CIN==1 && A==4'b1111 && B==4'b0000 && COUT==1 && SUM==4'b0000);
  // MSB generate case (A3=B3=1) forces COUT
  cover property (@(ev) A[3] && B[3] && COUT==1);
  // MSB kill with carry-in to MSB (COUT must be 0)
  cover property (@(ev) A[3]==0 && B[3]==0 && c3==1 && COUT==0);
  // Extreme sums
  cover property (@(ev) {COUT,SUM} == 5'd0);
  cover property (@(ev) {COUT,SUM} == 5'd31);
endmodule

// Checker for 1-bit full adder
module fa_sva (
  input logic A,
  input logic B,
  input logic CIN,
  input logic SUM,
  input logic COUT
);
  event ev;
  always @* if ($changed({A,B,CIN,SUM,COUT})) -> ev;

  // X/Z checks
  assert property (@(ev) !$isunknown({A,B,CIN,SUM,COUT}))
    else $error("X/Z detected in full_adder ports");

  // Truth-function checks
  assert property (@(ev) SUM  == (A ^ B ^ CIN))
    else $error("full_adder SUM mismatch");
  assert property (@(ev) COUT == ((A & B) | (A & CIN) | (B & CIN)))
    else $error("full_adder COUT mismatch");
  assert property (@(ev) {COUT, SUM} == A + B + CIN)
    else $error("full_adder result mismatch");

  // Cover all 8 input combinations
  cover property (@(ev) A==0 && B==0 && CIN==0);
  cover property (@(ev) A==0 && B==0 && CIN==1);
  cover property (@(ev) A==0 && B==1 && CIN==0);
  cover property (@(ev) A==0 && B==1 && CIN==1);
  cover property (@(ev) A==1 && B==0 && CIN==0);
  cover property (@(ev) A==1 && B==0 && CIN==1);
  cover property (@(ev) A==1 && B==1 && CIN==0);
  cover property (@(ev) A==1 && B==1 && CIN==1);
endmodule

// Bind checkers to DUTs
bind ripple_carry_adder rca_sva rca_chk (.A(A), .B(B), .CIN(CIN), .SUM(SUM), .COUT(COUT));
bind full_adder         fa_sva  fa_chk  (.A(A), .B(B), .CIN(CIN), .SUM(SUM), .COUT(COUT));