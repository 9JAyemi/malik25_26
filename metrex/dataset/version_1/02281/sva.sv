// SVA checker for my_module
module my_module_sva (
  input  logic        input1,
  input  logic        input2,
  input  logic [3:0]  input3,
  input  logic [3:0]  input4,
  input  logic [7:0]  input5,
  input  logic [7:0]  input6,
  input  logic [7:0]  input7,
  input  logic [7:0]  input8,
  input  logic [7:0]  input9,
  input  logic [7:0]  input10,
  input  logic [15:0] output1,
  input  logic [3:0]  sum1,
  input  logic [47:0] concat1
);

  // Combinational sampling on any relevant change
  event comb_ev = (input1 or input2 or input3 or input4 or input5 or input6 or input7 or input8 or input9 or input10 or output1 or sum1 or concat1);
  default clocking cb @ (comb_ev); endclocking

  // Local lets (purely combinational expectations)
  let base16        = input2 ? {15'b0, input1} : 16'h0000;
  let low16_concat  = {input9, input10};                            // concat1[15:0]
  let expected16    = base16 + low16_concat;                        // final output (16-bit trunc)
  let sum1_calc     = (input3 + input4) & 4'hF;                     // 4-bit wrap
  let concat_calc   = {input5, input6, input7, input8, input9, input10};
  let expected52    = {sum1_calc, concat_calc} + {36'b0, base16};   // full-width math
  let sum5          = {1'b0, input3} + {1'b0, input4};              // for overflow cover
  let sum17         = {1'b0, base16} + {1'b0, low16_concat};        // 16-bit add carry

  // Functional equivalence of output (only low 16 bits matter)
  a_func:        assert property (output1 == expected16);

  // Internal computations match specification
  a_sum1:        assert property (sum1   == sum1_calc);
  a_concat:      assert property (concat1== concat_calc);

  // Consistency check against full-width computation
  a_trunc_cons:  assert property (output1 == expected52[15:0]);

  // Known-propagation: if inputs are known, output must be known
  a_known:       assert property (!$isunknown({input1,input2,input3,input4,input5,input6,input7,input8,input9,input10}) |-> !$isunknown(output1));

  // Non-interference: upper bytes and sum1 must not affect output1
  a_nonint:      assert property ($stable({input1,input2,input9,input10}) && $changed({input3,input4,input5,input6,input7,input8}) |-> $stable(output1));

  // Coverage
  c_input2_0:    cover property (input2==1'b0);
  c_input2_1_0:  cover property (input2==1'b1 && input1==1'b0);
  c_input2_1_1:  cover property (input2==1'b1 && input1==1'b1);
  c_sum1_wr:     cover property (sum5[4]);                          // sum1 overflow/wrap
  c_low16_cy:    cover property (sum17[16]);                         // carry out of low16 addition
  c_trunc_hi:    cover property (expected52[51:16] != 36'b0);        // high bits non-zero => truncation occurs

endmodule

// Bind into DUT (connect internal regs for checking)
bind my_module my_module_sva u_my_module_sva (
  .input1(input1), .input2(input2),
  .input3(input3), .input4(input4),
  .input5(input5), .input6(input6),
  .input7(input7), .input8(input8),
  .input9(input9), .input10(input10),
  .output1(output1),
  .sum1(sum1), .concat1(concat1)
);