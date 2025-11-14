// SVA bind file for nor_gate, full_adder, bitwise_and, and top_module
// Focused, high-quality checks with concise coverage

// ---------------- nor_gate ----------------
module nor_gate_sva (input logic a, b, out);
  // Functional correctness (true NOR) when inputs are known
  property p_nor_func;
    @(*) (!$isunknown({a,b})) |-> (out == ~(a | b) && !$isunknown(out));
  endproperty
  assert property (p_nor_func);

  // Input space coverage (4 combos)
  cover property (@(*) (a==0 && b==0));
  cover property (@(*) (a==0 && b==1));
  cover property (@(*) (a==1 && b==0));
  cover property (@(*) (a==1 && b==1));
endmodule
bind nor_gate nor_gate_sva u_nor_gate_sva (.a(a), .b(b), .out(out));

// ---------------- full_adder ----------------
module full_adder_sva (input logic a, b, cin, cout, sum);
  // Sum correctness
  property p_fa_sum;
    @(*) (!$isunknown({a,b,cin})) |-> (sum == (a ^ b ^ cin) && !$isunknown(sum));
  endproperty
  assert property (p_fa_sum);

  // Carry-out correctness (complete expression)
  property p_fa_cout;
    @(*) (!$isunknown({a,b,cin})) |-> (cout == ((a & b) | (a & cin) | (b & cin)) && !$isunknown(cout));
  endproperty
  assert property (p_fa_cout);

  // Full 8-combo input coverage
  generate
    genvar ia, ib, ic;
    for (ia=0; ia<2; ia++) begin : COV_A
      for (ib=0; ib<2; ib++) begin : COV_B
        for (ic=0; ic<2; ic++) begin : COV_C
          cover property (@(*) (a==ia && b==ib && cin==ic));
        end
      end
    end
  endgenerate
endmodule
bind full_adder full_adder_sva u_full_adder_sva (.a(a), .b(b), .cin(cin), .cout(cout), .sum(sum));

// ---------------- bitwise_and ----------------
module bitwise_and_sva (input logic [1:0] a, b, out);
  // Bitwise AND correctness on both bits
  property p_bw_and;
    @(*) (!$isunknown({a,b})) |-> (out == (a & b) && !$isunknown(out));
  endproperty
  assert property (p_bw_and);

  // Output pattern coverage (00, 01, 10, 11)
  cover property (@(*) (!$isunknown({a,b})) && (a==2'b00) && (b==2'b00));
  cover property (@(*) (!$isunknown({a,b})) && (a==2'b01) && (b==2'b01));
  cover property (@(*) (!$isunknown({a,b})) && (a==2'b10) && (b==2'b10));
  cover property (@(*) (!$isunknown({a,b})) && (a==2'b11) && (b==2'b11));
  // Ensure MSB path can be 1 (catches the hard-coded MSB bug)
  cover property (@(*) (!$isunknown({a,b})) && (a[1] & b[1]));
endmodule
bind bitwise_and bitwise_and_sva u_bitwise_and_sva (.a(a), .b(b), .out(out));

// ---------------- top_module (end-to-end) ----------------
module top_module_sva (
  input logic a, b, cin,
  input logic cout, sum,
  input logic [1:0] final_output
);
  // End-to-end intent: NOR(a,b), full-adder sum/cout, AND path formation
  property p_top_e2e;
    @(*) (!$isunknown({a,b,cin})) |->
      (sum == (a ^ b ^ cin)) &&
      (cout == ((a & b) | (a & cin) | (b & cin))) &&
      (final_output == {1'b0, (~(a | b) & (a ^ b ^ cin))}) &&
      !$isunknown({sum, cout, final_output});
  endproperty
  assert property (p_top_e2e);

  // Interesting end-to-end coverage
  // LSB of final_output goes high (requires a=0,b=0,cin=1)
  cover property (@(*) (a==0 && b==0 && cin==1 && final_output==2'b01));
  // Carry generate (a=b=1,cin=0) and carry propagate (a^b=1,cin=1)
  cover property (@(*) (a==1 && b==1 && cin==0 && cout==1));
  cover property (@(*) ((a^b)==1 && cin==1 && cout==1));
endmodule
bind top_module top_module_sva u_top_module_sva (
  .a(a), .b(b), .cin(cin),
  .cout(cout), .sum(sum),
  .final_output(final_output)
);