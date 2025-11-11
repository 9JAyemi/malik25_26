// SVA checker for adder_4bit (combinational, sampled on any input change with ##0 settle)
module adder_4bit_sva (
  input  logic [3:0] a,
  input  logic [3:0] b,
  input  logic       cin,
  input  logic [3:0] sum,
  input  logic       cout,
  input  logic [2:0] carry
);
  default clocking cb @(a or b or cin); endclocking

  // No X/Z on outputs when inputs known
  ap_known: assert property (!$isunknown({a,b,cin}) |-> ##0 !$isunknown({sum,cout,carry}));

  // Bit sums
  ap_s0: assert property (1 |-> ##0 sum[0] == (a[0]^b[0]^cin));
  ap_s1: assert property (1 |-> ##0 sum[1] == (a[1]^b[1]^carry[0]));
  ap_s2: assert property (1 |-> ##0 sum[2] == (a[2]^b[2]^carry[1]));
  ap_s3: assert property (1 |-> ##0 sum[3] == (a[3]^b[3]^carry[2]));

  // Carries (canonical form)
  ap_c0: assert property (1 |-> ##0 carry[0] == ((a[0]&b[0]) | ((a[0]^b[0]) & cin)));
  ap_c1: assert property (1 |-> ##0 carry[1] == ((a[1]&b[1]) | ((a[1]^b[1]) & carry[0])));
  ap_c2: assert property (1 |-> ##0 carry[2] == ((a[2]&b[2]) | ((a[2]^b[2]) & carry[1])));

  // Cout and end-to-end equivalence
  ap_cout: assert property (1 |-> ##0 cout == ((a[3]&b[3]) | ((a[3]^b[3]) & carry[2])));
  ap_e2e:  assert property (1 |-> ##0 {cout,sum} == a + b + cin);

  // Lightweight functional coverage
  cp_no_carry: cover property (1 |-> ##0 (!carry[0] && !carry[1] && !carry[2] && !cout));
  cp_ripple:   cover property (1 |-> ##0 (carry[0] && carry[1] && carry[2] && cout));
  cp_zero:     cover property (1 |-> ##0 {cout,sum} == 5'd0);
  cp_max:      cover property (1 |-> ##0 {cout,sum} == 5'd31);
endmodule

// Bind into DUT (accesses internal 'carry' wire)
bind adder_4bit adder_4bit_sva chk (
  .a(a), .b(b), .cin(cin), .sum(sum), .cout(cout), .carry(carry)
);