// SVA for ADDER4 (combinational checker; bind into DUT)
// Focus: correctness, X-prop, and key coverage (carry/no-carry, edges, ripple)
module ADDER4_sva_bind (
  input  logic [3:0] A,
  input  logic [3:0] B,
  input  logic       CIN,
  input  logic [3:0] SUM,
  input  logic       COUT
);
  logic [4:0] exp;

  always_comb begin
    exp = {1'b0, A} + {1'b0, B} + CIN;

    // Functional correctness (5-bit sum to catch carry correctly)
    assert ({COUT, SUM} == exp)
      else $error("ADDER4 mismatch: A=%0h B=%0h CIN=%0b got {COUT,SUM}=%0h exp=%0h",
                  A, B, CIN, {COUT,SUM}, exp);

    // No X/Z on outputs when inputs are known
    if (!$isunknown({A,B,CIN})) begin
      assert (!$isunknown({COUT,SUM}))
        else $error("ADDER4 X/Z on outputs with known inputs: A=%0h B=%0h CIN=%0b SUM=%0h COUT=%0b",
                    A, B, CIN, SUM, COUT);
    end

    // Glitch/stability: outputs shouldn't change if inputs didn't
    if (!$isunknown({A,B,CIN}) && $stable({A,B,CIN})) begin
      assert ($stable({SUM,COUT}))
        else $error("ADDER4 outputs changed without input change: A=%0h B=%0h CIN=%0b", A,B,CIN);
    end

    // Coverage: carry/no-carry and key corner/ripple cases
    cover (COUT == 1'b0);
    cover (COUT == 1'b1);
    cover (A==4'h0 && B==4'h0 && CIN==1'b0);       // all zeros
    cover (A==4'hF && B==4'hF && CIN==1'b1);       // max + carry-in
    cover (A==4'hF && B==4'h1 && CIN==1'b0);       // long carry chain
    cover (A==4'h8 && B==4'h8 && CIN==1'b0);       // mid-bit generate
    cover ((exp[3:0] == 4'h0) && (COUT == 1'b1));  // wrap to zero with carry
  end
endmodule

// Bind into the DUT (no clock needed)
bind ADDER4 ADDER4_sva_bind u_adder4_sva_bind (.*);