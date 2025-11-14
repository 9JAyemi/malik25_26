// SVA checkers for add2 and add3. Bind these to the DUTs.
// Concise, high-quality functional checks plus essential coverage.

module add2_sva (
  input  logic [3:0] A,
  input  logic [3:0] B,
  input  logic [4:0] S
);
  logic [3:0] exp_sum;
  logic       exp_carry;

  always_comb begin
    exp_sum   = (A + B) & 4'hF;
    exp_carry = (exp_sum >= 4'd10);

    // Functional assertions
    assert (S[3:0] == exp_sum)
      else $error("add2 sum mismatch: A=%0d B=%0d exp=%0d got=%0d", A,B,exp_sum,S[3:0]);
    assert (S[4]   == exp_carry)
      else $error("add2 carry mismatch: A=%0d B=%0d exp=%0d got=%0d", A,B,exp_carry,S[4]);
    // Internal consistency (carry reflects low nibble)
    assert (S == { (S[3:0] >= 4'd10), S[3:0] })
      else $error("add2 S internal inconsistency: S=%b", S);

    // X/Z checks
    assert (!$isunknown({A,B})) else $error("add2 X/Z on inputs A/B");
    assert (!$isunknown(S))     else $error("add2 X/Z on output S");
  end

  // Essential coverage (exercise boundary and carry conditions)
  cover property (@(A or B)) (S[4]==1'b0);                       // no carry
  cover property (@(A or B)) (S[4]==1'b1);                       // carry
  cover property (@(A or B)) (S[3:0]==4'd0);
  cover property (@(A or B)) (S[3:0]==4'd9 && S[4]==1'b0);
  cover property (@(A or B)) (S[3:0]==4'd10 && S[4]==1'b1);
  cover property (@(A or B)) (S[3:0]==4'd15 && S[4]==1'b1);
endmodule


module add3_sva (
  input  logic [3:0] A,
  input  logic [3:0] B,
  input  logic [3:0] C,
  input  logic [4:0] S
);
  logic [3:0] exp_sum3;
  logic       exp_carry3;
  logic       stage1_carry;

  always_comb begin
    exp_sum3     = (A + B + C) & 4'hF;
    exp_carry3   = (exp_sum3 >= 4'd10);
    stage1_carry = (((A + B) & 4'hF) >= 4'd10);

    // Functional assertions (top-level behavior independent of hierarchy)
    assert (S[3:0] == exp_sum3)
      else $error("add3 sum mismatch: A=%0d B=%0d C=%0d exp=%0d got=%0d",
                  A,B,C,exp_sum3,S[3:0]);
    assert (S[4]   == exp_carry3)
      else $error("add3 carry mismatch: A=%0d B=%0d C=%0d exp=%0d got=%0d",
                  A,B,C,exp_carry3,S[4]);
    // Internal consistency (carry reflects low nibble)
    assert (S == { (S[3:0] >= 4'd10), S[3:0] })
      else $error("add3 S internal inconsistency: S=%b", S);

    // X/Z checks
    assert (!$isunknown({A,B,C})) else $error("add3 X/Z on inputs A/B/C");
    assert (!$isunknown(S))       else $error("add3 X/Z on output S");
  end

  // Coverage: overall and stage interactions
  cover property (@(A or B or C)) (S[4]==1'b0);                         // final no carry
  cover property (@(A or B or C)) (S[4]==1'b1);                         // final carry
  cover property (@(A or B or C)) (S[3:0]==4'd0);
  cover property (@(A or B or C)) (S[3:0]==4'd9  && S[4]==1'b0);
  cover property (@(A or B or C)) (S[3:0]==4'd10 && S[4]==1'b1);
  cover property (@(A or B or C)) (S[3:0]==4'd15 && S[4]==1'b1);

  // Stage interaction coverage (derived from inputs)
  cover property (@(A or B or C)) ( stage1_carry==0 && S[4]==0 );       // none
  cover property (@(A or B or C)) ( stage1_carry==1 && S[4]==0 );       // carry in stage1 only
  cover property (@(A or B or C)) ( stage1_carry==0 && S[4]==1 );       // carry in stage2 only
  cover property (@(A or B or C)) ( stage1_carry==1 && S[4]==1 );       // both
endmodule


// Bind checkers to DUTs
bind add2 add2_sva add2_chk (.*);
bind add3 add3_sva add3_chk (.*);