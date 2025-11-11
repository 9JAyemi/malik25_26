// SVA for full_adder. Bind this to the DUT.
// Uses input-edge sampling so assertions fire whenever inputs change.

module full_adder_sva_ports (
  input logic a, b, cin,
  input logic sum, carry
);
  default clocking cb @(posedge a or negedge a or posedge b or negedge b or posedge cin or negedge cin); endclocking

  // Truth-table equivalence
  assert property (sum   == (a ^ b ^ cin));
  assert property (carry == ((a & b) | (b & cin) | (a & cin)));

  // No X/Z on outputs when inputs are known
  assert property (!$isunknown({a,b,cin}) |-> !$isunknown({sum,carry}));

  // Basic coverage
  cover property (a==0 && b==0 && cin==0);
  cover property (a==0 && b==0 && cin==1);
  cover property (a==0 && b==1 && cin==0);
  cover property (a==0 && b==1 && cin==1);
  cover property (a==1 && b==0 && cin==0);
  cover property (a==1 && b==0 && cin==1);
  cover property (a==1 && b==1 && cin==0);
  cover property (a==1 && b==1 && cin==1);

  cover property (sum);
  cover property (carry);
endmodule


// Optional: check DUT internals for consistency
module full_adder_sva_int (
  input logic a, b, cin,
  input logic sum, carry,
  input logic w1, w2, w3
);
  default clocking cb @(posedge a or negedge a or posedge b or negedge b or posedge cin or negedge cin); endclocking

  // Internal definitions
  assert property (w1 == (a ^ b));
  assert property (w2 == (a & b));
  assert property (w3 == (w1 & cin));

  // Output construction from internals
  assert property (sum   == (w1 ^ cin));
  assert property (carry == (w2 | w3));

  // Generate vs propagate coverage
  cover property (w2);                 // generate
  cover property (w3);                 // propagate
  cover property (carry && !w2 && w3); // pure propagate
  cover property (carry && w2);        // generate present

  // No X/Z on internals when inputs are known
  assert property (!$isunknown({a,b,cin}) |-> !$isunknown({w1,w2,w3,sum,carry}));
endmodule


// Bind to the DUT
bind full_adder full_adder_sva_ports (.a(a), .b(b), .cin(cin), .sum(sum), .carry(carry));
bind full_adder full_adder_sva_int   (.a(a), .b(b), .cin(cin), .sum(sum), .carry(carry), .w1(w1), .w2(w2), .w3(w3));