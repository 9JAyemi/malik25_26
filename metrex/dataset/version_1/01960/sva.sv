// SVA checker for four_bit_adder
// Binds to DUT and checks functional correctness, X-propagation, and key corner coverage.
// Includes an optional assertion to flag the likely signed carry-in issue.

module four_bit_adder_sva #(parameter bit CHECK_CIN_AS_CARRYIN = 1) (
  input  signed [3:0] a,
  input  signed [3:0] b,
  input  signed       cin,
  input  signed [3:0] sum,
  input  signed       cout
);
  // Sample on any combinational change
  event comb_e; always @* -> comb_e;
  default clocking cb @(comb_e); endclocking

  // Golden computations
  logic signed [4:0] gold_signed;   // as-coded: signed add with sign-extended cin (0 or -1)
  logic signed [4:0] gold_carry1;   // expected carry-in behavior (+1) when cin==1

  always_comb begin
    gold_signed  = $signed({a[3],a}) + $signed({b[3],b}) + $signed({{4{cin[0]}}, cin[0]});
    gold_carry1  = $signed({a[3],a}) + $signed({b[3],b}) + 5'sd1;
  end

  // No X on outputs when inputs are known
  assert property ( (!$isunknown({a,b,cin})) |-> !$isunknown({sum,cout}) )
    else $error("four_bit_adder: X/Z on outputs with known inputs");

  // Functional equivalence to 5-bit signed sum (matches DUT as coded)
  assert property ( (!$isunknown({a,b,cin})) |-> ({cout,sum} == gold_signed) )
    else $error("four_bit_adder: {cout,sum} != signed(a)+signed(b)+signed(cin)");

  // Optional: flag carry-in semantics (cin==1 should mean +1, not -1)
  if (CHECK_CIN_AS_CARRYIN) begin
    assert property ( (!$isunknown({a,b,cin})) && (cin === 1'b1) |-> ({cout,sum} == gold_carry1) )
      else $error("four_bit_adder: cin==1 does not behave as +1 (signed cin likely causing -1)");
  end

  // Concise functional coverage of key scenarios
  cover property ( cin === 1'b0 );
  cover property ( cin === 1'b1 );

  // Signed overflow observed (two same-sign operands produce different sign sum)
  cover property ( !$isunknown({a,b,sum}) && (a[3] == b[3]) && (sum[3] != a[3]) );

  // Extremes
  cover property ( a == 4'sd7   && b == 4'sd7   );   // max + max
  cover property ( a == -4'sd8  && b == -4'sd8  );   // min + min
  cover property ( (a == 4'sd7  && b == -4'sd8) ||
                   (a == -4'sd8 && b == 4'sd7 ) );   // mixed extremes

  // Zero result
  cover property ( {cout,sum} == 5'sd0 );
endmodule

// Bind to DUT
bind four_bit_adder four_bit_adder_sva #(.CHECK_CIN_AS_CARRYIN(1)) four_bit_adder_sva_b (.*);