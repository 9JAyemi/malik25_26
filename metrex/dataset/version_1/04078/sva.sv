// SVA checker for pipelined_full_adder
// Bind this file without modifying the DUT

module pipelined_full_adder_sva (
  input logic [3:0] a,
  input logic [3:0] b,
  input logic [3:0] c,
  input logic [3:0] sum,
  input logic       cout
);

  logic [4:0] exp;

  always_comb begin
    exp = $unsigned(a) + $unsigned(b) + $unsigned(c);

    // X/Z sanitation
    assert (!$isunknown({a,b,c})) else $error("pipelined_full_adder: X/Z on inputs");
    assert (!$isunknown({sum,cout})) else $error("pipelined_full_adder: X/Z on outputs");

    // Functional equivalence
    assert ({cout,sum} == exp)
      else $error("pipelined_full_adder: {cout,sum} != a+b+c exp=%0d got={%0b,%0h}", exp, cout, sum);

    // Redundant but precise field checks
    assert (sum  == exp[3:0]) else $error("pipelined_full_adder: sum mismatch");
    assert (cout == exp[4])   else $error("pipelined_full_adder: cout mismatch");

    // Concise functional coverage
    cover (a==4'h0 && b==4'h0 && c==4'h0);            // all zeros
    cover (a==4'hF && b==4'h0 && c==4'h0);            // max + 0
    cover (a==4'hF && b==4'h1 && c==4'h0);            // boundary to overflow
    cover (a==4'h8 && b==4'h7 && c==4'h0);            // mixed pattern, no overflow
    cover (a==4'hF && b==4'hF && c==4'hF);            // max + max + max
    cover (cout==1'b0);                                // no overflow seen
    cover (cout==1'b1);                                // overflow seen
    cover (sum==4'h0);                                 // zero sum
    cover (sum==4'hF);                                 // max sum field
  end

endmodule

bind pipelined_full_adder pipelined_full_adder_sva sva_inst (.*);