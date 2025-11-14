// SVA checker for two_input_module (clockless, combinational)
module two_input_module_sva (
  input logic input1, input2, input3, input4, input5, input6, input7,
  input logic output1
);
  // Local predicates
  wire p1  = input1 && input2;
  wire p2  = input3 && input4;
  wire p3  = input5 && input6;
  wire any = p1 || p2 || p3;

  // Functional equivalence (primary check)
  a_func: assert property ( output1 == any );

  // Explicit independence from input7 and default cases
  a_no_pairs_zero: assert property ( !any |-> !output1 );
  a_pairs_dominate_7: assert property ( input7 && any |-> output1 );
  a_7_only_zero: assert property ( input7 && !any |-> !output1 );

  // X-propagation safety: when inputs are known, output is known
  a_known_inputs_known_out: assert property ( !($isunknown({input1,input2,input3,input4,input5,input6,input7})) |-> !$isunknown(output1) );

  // Coverage: hit each branch, overlap, and tie-break scenarios (with expected output)
  c_p1:        cover property ( p1 &&  output1 );
  c_p2:        cover property ( p2 &&  output1 );
  c_p3:        cover property ( p3 &&  output1 );
  c_7_only:    cover property ( input7 && !any && !output1 );
  c_else:      cover property ( !input7 && !any && !output1 );
  c_overlap12: cover property ( (p1 && p2) && output1 );
  c_all3:      cover property ( (p1 && p2 && p3) && output1 );
  c_pair_with7:cover property ( any && input7 && output1 );
endmodule

// Bind into the DUT
bind two_input_module two_input_module_sva sva_i(.*);