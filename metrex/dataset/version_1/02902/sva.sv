// Assertions and coverage for AND4
// Usage: provide a sampling clock that is slower than the gate propagation so inputs are stable
// across a sample. Optionally tune D12/D34 (latency bounds in cycles) to match your env.
module AND4_sva #(
  parameter int unsigned D12 = 2,  // cycles allowed for in1/in2 to affect out1
  parameter int unsigned D34 = 1   // cycles allowed for in3/in4 to affect out1
)(
  input  logic clk,
  input  logic in1, in2, in3, in4,
  input  logic out1
);

  default clocking cb @ (posedge clk); endclocking

  // Helpers
  function automatic bit all_known4(logic a,b,c,d);
    return !$isunknown({a,b,c,d});
  endfunction
  function automatic bit all_known5(logic a,b,c,d,e);
    return !$isunknown({a,b,c,d,e});
  endfunction

  // Functional correctness when inputs have settled (no false failures due to gate delays)
  // If inputs did not change between samples and are known, out1 must equal the 4-way AND.
  property p_func_when_stable;
    all_known5(in1,in2,in3,in4,out1) && $stable({in1,in2,in3,in4})
      |-> out1 === (in1 & in2 & in3 & in4);
  endproperty
  assert property (p_func_when_stable);

  // No X/Z on output when all inputs are 0/1 and stable
  property p_no_x_on_known_inputs;
    all_known4(in1,in2,in3,in4) && $stable({in1,in2,in3,in4})
      |-> (out1 !== 1'bx && out1 !== 1'bz);
  endproperty
  assert property (p_no_x_on_known_inputs);

  // Out1 cannot be 1 unless all inputs are 1 (after settling)
  property p_one_implies_all_ones;
    all_known5(in1,in2,in3,in4,out1) && $stable({in1,in2,in3,in4,out1}) && out1
      |-> (in1 && in2 && in3 && in4);
  endproperty
  assert property (p_one_implies_all_ones);

  // No glitches: if inputs remain stable across two samples, out must also be stable
  property p_no_glitch_when_inputs_stable;
    $stable({in1,in2,in3,in4}) && $past($stable({in1,in2,in3,in4}))
      |-> $stable(out1);
  endproperty
  assert property (p_no_glitch_when_inputs_stable);

  // Latency covers (not asserts) to track expected propagation windows
  // in3/in4 edges should be observed on out1 within D34 cycles when others are 1
  cover property (in1 && in2 && in4 && $rose(in3) |-> ##[1:D34] $rose(out1));
  cover property (in1 && in2 && in4 && $fell(in3) |-> ##[1:D34] $fell(out1));
  cover property (in1 && in2 && in3 && $rose(in4) |-> ##[1:D34] $rose(out1));
  cover property (in1 && in2 && in3 && $fell(in4) |-> ##[1:D34] $fell(out1));

  // in1/in2 edges should be observed on out1 within D12 cycles when others are 1
  cover property (in2 && in3 && in4 && $rose(in1) |-> ##[1:D12] $rose(out1));
  cover property (in2 && in3 && in4 && $fell(in1) |-> ##[1:D12] $fell(out1));
  cover property (in1 && in3 && in4 && $rose(in2) |-> ##[1:D12] $rose(out1));
  cover property (in1 && in3 && in4 && $fell(in2) |-> ##[1:D12] $fell(out1));

  // Functional state coverage: see all 16 input combinations and correct out1
  cover property ( $stable({in1,in2,in3,in4}) && {in1,in2,in3,in4} == 4'b0000 && out1==1'b0 );
  cover property ( $stable({in1,in2,in3,in4}) && {in1,in2,in3,in4} == 4'b0001 && out1==1'b0 );
  cover property ( $stable({in1,in2,in3,in4}) && {in1,in2,in3,in4} == 4'b0010 && out1==1'b0 );
  cover property ( $stable({in1,in2,in3,in4}) && {in1,in2,in3,in4} == 4'b0011 && out1==1'b0 );
  cover property ( $stable({in1,in2,in3,in4}) && {in1,in2,in3,in4} == 4'b0100 && out1==1'b0 );
  cover property ( $stable({in1,in2,in3,in4}) && {in1,in2,in3,in4} == 4'b0101 && out1==1'b0 );
  cover property ( $stable({in1,in2,in3,in4}) && {in1,in2,in3,in4} == 4'b0110 && out1==1'b0 );
  cover property ( $stable({in1,in2,in3,in4}) && {in1,in2,in3,in4} == 4'b0111 && out1==1'b0 );
  cover property ( $stable({in1,in2,in3,in4}) && {in1,in2,in3,in4} == 4'b1000 && out1==1'b0 );
  cover property ( $stable({in1,in2,in3,in4}) && {in1,in2,in3,in4} == 4'b1001 && out1==1'b0 );
  cover property ( $stable({in1,in2,in3,in4}) && {in1,in2,in3,in4} == 4'b1010 && out1==1'b0 );
  cover property ( $stable({in1,in2,in3,in4}) && {in1,in2,in3,in4} == 4'b1011 && out1==1'b0 );
  cover property ( $stable({in1,in2,in3,in4}) && {in1,in2,in3,in4} == 4'b1100 && out1==1'b0 );
  cover property ( $stable({in1,in2,in3,in4}) && {in1,in2,in3,in4} == 4'b1101 && out1==1'b0 );
  cover property ( $stable({in1,in2,in3,in4}) && {in1,in2,in3,in4} == 4'b1110 && out1==1'b0 );
  cover property ( $stable({in1,in2,in3,in4}) && {in1,in2,in3,in4} == 4'b1111 && out1==1'b1 );

  // Output toggle coverage
  cover property ($rose(out1));
  cover property ($fell(out1));

endmodule

// Optional bind example (provide a sampling clock 'clk'):
// bind AND4 AND4_sva sva_u (.*,.clk(testbench_clk));