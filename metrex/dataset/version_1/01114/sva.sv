// SVA checker for adder_subtractor (bindable, no DUT edits required)
module adder_subtractor_sva (
  input  logic [3:0] A,
  input  logic [3:0] B,
  input  logic       SUB,
  input  logic [3:0] S,
  input  logic       OVF,
  // internal DUT nets (visible via bind)
  input  logic [3:0] B_neg,
  input  logic       C_in
);

  // Combinational correctness checks
  always @* begin
    // Sanity: no X/Z on I/O
    assert (!$isunknown({A,B,SUB})) else
      $error("adder_subtractor: X/Z on inputs A=%h B=%h SUB=%b", A,B,SUB);
    assert (!$isunknown({S,OVF})) else
      $error("adder_subtractor: X/Z on outputs S=%h OVF=%b", S,OVF);

    // Golden model
    logic [4:0] add_ext, sub_ext;
    logic [3:0] exp_add_s, exp_sub_s;
    logic       exp_add_cout, exp_sub_borrow;
    logic       exp_add_ovf,  exp_sub_ovf;

    add_ext        = {1'b0, A} + {1'b0, B};
    sub_ext        = {1'b0, A} - {1'b0, B};
    exp_add_s      = add_ext[3:0];
    exp_sub_s      = sub_ext[3:0];
    exp_add_cout   = add_ext[4];
    exp_sub_borrow = sub_ext[4]; // 1 when A < B (unsigned borrow)
    exp_add_ovf    = (A[3] == B[3]) && (exp_add_s[3] != A[3]); // signed add overflow
    exp_sub_ovf    = (A[3] != B[3]) && (exp_sub_s[3] != A[3]); // signed sub overflow

    // Functional equivalence (mode-select)
    assert ((SUB==1'b0 && (S==exp_add_s) && (OVF==exp_add_ovf)) ||
            (SUB==1'b1 && (S==exp_sub_s) && (OVF==exp_sub_ovf))) else
      $error("adder_subtractor: wrong S/OVF. A=%h B=%h SUB=%b S=%h OVF=%b expS(add=%h sub=%h) expOVF(add=%b sub=%b)",
             A,B,SUB,S,OVF,exp_add_s,exp_sub_s,exp_add_ovf,exp_sub_ovf);

    // Internal: B_neg matches 2's complement when SUB=1, passthru when SUB=0
    assert ((SUB==1'b0 && B_neg==B) ||
            (SUB==1'b1 && B_neg==(~B + 4'd1))) else
      $error("adder_subtractor: B_neg wrong. SUB=%b B=%h B_neg=%h", SUB,B,B_neg);

    // Internal: C_in behaves like borrow indicator for SUB, 0 for ADD
    assert ((SUB==1'b0 && C_in==1'b0) ||
            (SUB==1'b1 && C_in==exp_sub_borrow)) else
      $error("adder_subtractor: C_in wrong. A=%h B=%h SUB=%b C_in=%b exp_borrow=%b",
             A,B,SUB,C_in,exp_sub_borrow);
  end

  // Lightweight functional coverage
  always @* begin
    cover (SUB==0);
    cover (SUB==1);

    // Addition space
    cover (SUB==0 && exp_add_ovf);
    cover (SUB==0 && !exp_add_ovf);
    cover (SUB==0 && exp_add_cout);

    // Subtraction space
    cover (SUB==1 && exp_sub_ovf);
    cover (SUB==1 && !exp_sub_ovf);
    cover (SUB==1 && exp_sub_borrow);
    cover (SUB==1 && A==B && S==4'h0 && OVF==1'b0);

    // Corners
    cover (S==4'h0);
    cover (S==4'hF);
    cover (A inside {4'h0,4'h7,4'h8,4'hF});
    cover (B inside {4'h0,4'h7,4'h8,4'hF});
  end
endmodule

// Bind the checker into every instance of the DUT
bind adder_subtractor adder_subtractor_sva
(
  .A(A), .B(B), .SUB(SUB), .S(S), .OVF(OVF),
  .B_neg(B_neg), .C_in(C_in)
);