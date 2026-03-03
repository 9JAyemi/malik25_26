// SVA checker for five_to_one
// Bind this to the DUT and hook up a sampling clock/reset from your env.

module five_to_one_sva (
  input logic clk,
  input logic rst_n,

  input  logic input1,
  input  logic input2,
  input  logic input3,
  input  logic input4,
  input  logic input5,
  input  logic output1
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  // Golden functional equivalence (primary check)
  property p_func_eq;
    output1 === ((input1 & input2) | ((input3 & input4) & input5));
  endproperty
  a_func_eq: assert property (p_func_eq);

  // If all inputs are known, output must be known (X/Z clean)
  a_known: assert property (
    !$isunknown({input1,input2,input3,input4,input5}) |-> !$isunknown(output1)
  );

  // With inputs stable across a cycle, output must be stable (purely combinational)
  a_stable: assert property (
    $stable({input1,input2,input3,input4,input5}) |=> $stable(output1)
  );

  // Minimal yet meaningful functional coverage
  // Output low case
  c_low:   cover property ( !((input1 & input2) | ((input3 & input4) & input5)) );

  // Each OR-leg exclusively drives output high
  c_and1_only: cover property ( (input1 & input2) && !(input3 & input4 & input5) );
  c_and3_only: cover property ( !(input1 & input2) &&  (input3 & input4 & input5) );

  // Both legs high simultaneously
  c_both:  cover property ( (input1 & input2) && (input3 & input4 & input5) );

  // Output edge coverage
  c_rise:  cover property ( $rose(output1) );
  c_fall:  cover property ( $fell(output1) );

endmodule

// Example bind (put in your TB; provide a clock/reset from your environment)
// bind five_to_one five_to_one_sva u_five_to_one_sva (
//   .clk   (clk),
//   .rst_n (rst_n),
//   .input1(input1),
//   .input2(input2),
//   .input3(input3),
//   .input4(input4),
//   .input5(input5),
//   .output1(output1)
// );