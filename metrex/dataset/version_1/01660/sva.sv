// SVA checker for full_adder
module full_adder_sva (
  input logic a, b, cin,
  input logic cout, sum
);

  // Sample on any input toggle
  default clocking cb @(posedge a or negedge a or
                        posedge b or negedge b or
                        posedge cin or negedge cin); endclocking

  // Inputs must be 0/1 only
  ap_inputs_known: assert property (!$isunknown({a,b,cin}))
    else $error("full_adder: X/Z on inputs");

  // When inputs are known, outputs must be known and correct
  ap_sum2_correct: assert property (
      !$isunknown({a,b,cin}) |-> (!$isunknown({cout,sum}) &&
                                  {cout,sum} == (a + b + cin))
    ) else $error("full_adder: {cout,sum} != a+b+cin");

  // Redundant but explicit forms (parity and majority)
  ap_sum_parity:   assert property (
      !$isunknown({a,b,cin}) |-> (sum  == (a ^ b ^ cin))
    ) else $error("full_adder: sum != a^b^cin");

  ap_cout_majority: assert property (
      !$isunknown({a,b,cin}) |-> (cout == ((a & b) | (a & cin) | (b & cin)))
    ) else $error("full_adder: cout majority mismatch");

  // Functional coverage: all input combinations and expected outputs
  cp_000: cover property (!$isunknown({a,b,cin}) && {a,b,cin}==3'b000 && {cout,sum}==2'b00);
  cp_001: cover property (!$isunknown({a,b,cin}) && {a,b,cin}==3'b001 && {cout,sum}==2'b01);
  cp_010: cover property (!$isunknown({a,b,cin}) && {a,b,cin}==3'b010 && {cout,sum}==2'b01);
  cp_011: cover property (!$isunknown({a,b,cin}) && {a,b,cin}==3'b011 && {cout,sum}==2'b10);
  cp_100: cover property (!$isunknown({a,b,cin}) && {a,b,cin}==3'b100 && {cout,sum}==2'b01);
  cp_101: cover property (!$isunknown({a,b,cin}) && {a,b,cin}==3'b101 && {cout,sum}==2'b10);
  cp_110: cover property (!$isunknown({a,b,cin}) && {a,b,cin}==3'b110 && {cout,sum}==2'b10);
  cp_111: cover property (!$isunknown({a,b,cin}) && {a,b,cin}==3'b111 && {cout,sum}==2'b11);

endmodule

// Bind into the DUT
bind full_adder full_adder_sva u_full_adder_sva (
  .a(a), .b(b), .cin(cin), .cout(cout), .sum(sum)
);