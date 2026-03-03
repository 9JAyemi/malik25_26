// SVA for ripple_carry_adder and full_adder
// Bind-only; no DUT changes required.

module ripple_carry_adder_sva (
  input  logic [3:0] a,
  input  logic [3:0] b,
  input  logic       cin,
  input  logic [3:0] sum,
  input  logic       cout
);
  clocking cb @(*); endclocking
  default clocking cb;

  function automatic bit in_x();  return $isunknown({a,b,cin});          endfunction
  function automatic bit any_x(); return $isunknown({a,b,cin,sum,cout}); endfunction

  // Derived carry chain from inputs only (no need to see internal nets)
  logic c1, c2, c3;
  assign c1 = (a[0]&b[0]) | ((a[0]^b[0]) & cin);
  assign c2 = (a[1]&b[1]) | ((a[1]^b[1]) & c1);
  assign c3 = (a[2]&b[2]) | ((a[2]^b[2]) & c2);

  // Golden arithmetic equivalence
  assert property ( disable iff (in_x()) {cout,sum} == a + b + cin );

  // Bitwise ripple correctness
  assert property ( disable iff (in_x())
      (sum[0] == (a[0]^b[0]^cin)) &&
      (sum[1] == (a[1]^b[1]^c1 )) &&
      (sum[2] == (a[2]^b[2]^c2 )) &&
      (sum[3] == (a[3]^b[3]^c3 )) &&
      (cout    == ((a[3]&b[3]) | ((a[3]^b[3]) & c3)))
  );

  // Outputs must be known when inputs are known
  assert property ( disable iff (in_x()) !$isunknown({sum,cout}) );

  // Targeted functional coverage
  cover property ( !any_x() && a==4'h0 && b==4'h0 && cin==1'b0 && sum==4'h0 && cout==1'b0 ); // zero add
  cover property ( !any_x() && a==4'hF && b==4'hF && cin==1'b1 && sum==4'hF && cout==1'b1 ); // max + overflow
  cover property ( !any_x() && (a^b)==4'hF && (a&b)==4'h0 && cin==1'b1 && sum==4'h0 && cout==1'b1 ); // full propagate chain
  cover property ( !any_x() && (a&b)==4'h0 && cin==1'b0 && sum==(a^b) && cout==1'b0 ); // no generate, no carry
  cover property ( !any_x() && a==4'b0111 && b==4'b0000 && cin==1'b1 && sum==4'b1000 && cout==1'b0 ); // multi-bit ripple, no overflow
endmodule

bind ripple_carry_adder ripple_carry_adder_sva rca_sva_i (.*);


// Optional: per-cell SVA for full_adder (useful if reused elsewhere)
module full_adder_sva (
  input  logic a,
  input  logic b,
  input  logic cin,
  input  logic sum,
  input  logic cout
);
  clocking cb @(*); endclocking
  default clocking cb;

  function automatic bit in_x(); return $isunknown({a,b,cin}); endfunction

  assert property ( disable iff (in_x()) {cout,sum} == a + b + cin );
  assert property ( disable iff (in_x())
                    (sum == (a^b^cin)) &&
                    (cout == ((a&b) | ((a^b)&cin))) );

  cover property ( !$isunknown({a,b,cin,sum,cout}) && a==0 && b==0 && cin==0 && sum==0 && cout==0 );
  cover property ( !$isunknown({a,b,cin,sum,cout}) && a==1 && b==1 && cin==1 && sum==1 && cout==1 );
endmodule

bind full_adder full_adder_sva fa_sva_i (.*);