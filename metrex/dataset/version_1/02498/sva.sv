// SVA for adder4 and full_adder. Bind these to the DUTs.
// Focused, concise, and checks/coverage of core functionality.

module adder4_sva (
  input  [3:0] a,
  input  [3:0] b,
  input        cin,
  input  [3:0] sum,
  input        cout,
  input  [3:0] temp_sum,
  input        c1, c2, c3
);
  // Helper wires
  wire [3:0] G = a & b;
  wire [3:0] P = a ^ b;

  // Overall arithmetic correctness
  assert property (@(a or b or cin) {cout, sum} == a + b + cin);

  // Internal stage correctness (sum and carry)
  assert property (@(a or b or cin) temp_sum[0] == (a[0] ^ b[0] ^ cin));
  assert property (@(a or b or cin) c1 == ((a[0] & b[0]) | (cin & a[0]) | (cin & b[0])));

  assert property (@(a or b or cin) temp_sum[1] == (a[1] ^ b[1] ^ c1));
  assert property (@(a or b or cin) c2 == ((a[1] & b[1]) | (c1 & a[1]) | (c1 & b[1])));

  assert property (@(a or b or cin) temp_sum[2] == (a[2] ^ b[2] ^ c2));
  assert property (@(a or b or cin) c3 == ((a[2] & b[2]) | (c2 & a[2]) | (c2 & b[2])));

  assert property (@(a or b or cin) temp_sum[3] == (a[3] ^ b[3] ^ c3));
  assert property (@(a or b or cin) cout == ((a[3] & b[3]) | (c3 & a[3]) | (c3 & b[3])));

  // Output aliasing
  assert property (@(a or b or cin) sum == temp_sum);

  // Carry-lookahead equivalence (ripple chain integrity)
  assert property (@(a or b or cin) c1   == (G[0] | (P[0] & cin)));
  assert property (@(a or b or cin) c2   == (G[1] | (P[1]&G[0]) | (P[1]&P[0]&cin)));
  assert property (@(a or b or cin) c3   == (G[2] | (P[2]&G[1]) | (P[2]&P[1]&G[0]) | (P[2]&P[1]&P[0]&cin)));
  assert property (@(a or b or cin) cout == (G[3] | (P[3]&G[2]) | (P[3]&P[2]&G[1]) | (P[3]&P[2]&P[1]&G[0]) | (P[3]&P[2]&P[1]&P[0]&cin)));

  // No X/Z on outputs when inputs are known
  assert property (@(a or b or cin) (!$isunknown({a,b,cin})) |-> !$isunknown({sum,cout,temp_sum,c1,c2,c3}));

  // Coverage (key scenarios)
  cover property (@(a or b or cin) (!cin && !cout));                      // no carry
  cover property (@(a or b or cin) (!cin && cout));                       // carry from A+B
  cover property (@(a or b or cin) (cin && !cout));                       // carry-in absorbed
  cover property (@(a or b or cin) (cin && cout));                        // carry-in produces carry-out
  cover property (@(a or b or cin) (&P && cin && cout));                  // full propagate chain ripple
  cover property (@(a or b or cin) (a==4'h0 && b==4'h0 && !cin));         // baseline zero
  cover property (@(a or b or cin) (a==4'hF && b==4'hF && cin));          // worst-case overflow
endmodule

bind adder4 adder4_sva adder4_sva_b (.*);


// Focused SVA for full_adder cell
module full_adder_sva (
  input a, b, cin,
  input sum, cout
);
  // Functional truth
  assert property (@(a or b or cin) sum  == (a ^ b ^ cin));
  assert property (@(a or b or cin) cout == ((a & b) | (cin & a) | (cin & b)));

  // No X/Z on outputs when inputs are known
  assert property (@(a or b or cin) (!$isunknown({a,b,cin})) |-> !$isunknown({sum,cout}));

  // Basic coverage
  cover property (@(a or b or cin) cout);
  cover property (@(a or b or cin) !cout);
  cover property (@(a or b or cin) sum);
  cover property (@(a or b or cin) !sum);
endmodule

bind full_adder full_adder_sva full_adder_sva_b (.*);