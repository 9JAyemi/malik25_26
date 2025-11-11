// SVA bind module for calculator
module calculator_sva (
    input  logic        clk,
    input  logic        rst,
    input  logic [1:0]  op,
    input  logic [3:0]  num1,
    input  logic [3:0]  num2,
    input  logic [3:0]  result,
    input  logic        overflow
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Helpers
  function automatic logic [4:0] add5 (logic [3:0] a, b); add5 = a + b; endfunction
  function automatic logic [4:0] sub5 (logic [3:0] a, b); sub5 = {1'b0,a} - {1'b0,b}; endfunction
  function automatic logic [7:0] mul8 (logic [3:0] a, b); mul8 = a * b; endfunction

  // Sanity: inputs/outputs known
  a_inputs_known:  assert property (!$isunknown({op,num1,num2})));
  a_outputs_known: assert property (!$isunknown({result,overflow})));

  // Safety: no divide-by-zero
  a_no_div0: assert property (!(op==2'b11 && num2==4'd0)));

  // Functional correctness per op
  a_add: assert property (op==2'b00 |-> (result == add5(num1,num2)[3:0] &&
                                         overflow == add5(num1,num2)[4]));
  a_sub: assert property (op==2'b01 |-> (result == sub5(num1,num2)[3:0] &&
                                         overflow == sub5(num1,num2)[4]));
  a_mul: assert property (op==2'b10 |-> (result == mul8(num1,num2)[3:0] &&
                                         overflow == |mul8(num1,num2)[7:4]));
  a_div: assert property ((op==2'b11 && num2!=4'd0) |-> (result == (num1/num2) &&
                                                         overflow == 1'b0));

  // Minimal functional coverage
  c_add:       cover property (op==2'b00);
  c_sub:       cover property (op==2'b01);
  c_mul:       cover property (op==2'b10);
  c_div:       cover property (op==2'b11 && num2!=0);
  c_add_ovf:   cover property (op==2'b00 && add5(num1,num2)[4]);
  c_sub_borr:  cover property (op==2'b01 && sub5(num1,num2)[4]);
  c_mul_ovf:   cover property (op==2'b10 && |mul8(num1,num2)[7:4]);
  c_div0_try:  cover property (op==2'b11 && num2==0); // illegal; should not hit with a_no_div0
endmodule

bind calculator calculator_sva sva_i (.*);