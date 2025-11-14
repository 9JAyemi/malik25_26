// SVA checker for full_adder. Provide/route a sampling clock when binding.
checker full_adder_sva(input logic a,b,cin,sum,cout, input logic clk);
  default clocking @(posedge clk); endclocking

  // No X/Z on interface
  a_no_xz: assert property (!$isunknown({a,b,cin,sum,cout}));

  // Golden functionality
  a_add:   assert property ({cout,sum} == a + b + cin);

  // Equivalent boolean forms (guard against alternative implementation bugs)
  a_sum:   assert property (sum  == (a ^ b) ^ cin);
  a_cout:  assert property (cout == ((a & b) | (a & cin) | (b & cin)));

  // Stability: if inputs don’t change across a cycle, outputs must not change
  a_stable: assert property ($stable({a,b,cin}) |-> $stable({sum,cout}));

  // Functional coverage: all input combinations
  c_abc_000: cover property ({a,b,cin} == 3'b000);
  c_abc_001: cover property ({a,b,cin} == 3'b001);
  c_abc_010: cover property ({a,b,cin} == 3'b010);
  c_abc_011: cover property ({a,b,cin} == 3'b011);
  c_abc_100: cover property ({a,b,cin} == 3'b100);
  c_abc_101: cover property ({a,b,cin} == 3'b101);
  c_abc_110: cover property ({a,b,cin} == 3'b110);
  c_abc_111: cover property ({a,b,cin} == 3'b111);

  // Output space coverage
  c_out_00: cover property ({cout,sum} == 2'b00);
  c_out_01: cover property ({cout,sum} == 2'b01);
  c_out_10: cover property ({cout,sum} == 2'b10);
  c_out_11: cover property ({cout,sum} == 2'b11);
endchecker

// Bind example (connect clk from your environment)
bind full_adder full_adder_sva u_full_adder_sva(.a(a),.b(b),.cin(cin),.sum(sum),.cout(cout),.clk(clk));