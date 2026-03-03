// SVA for priority_encoder and final_output_generator
// Concise, high-quality checks with targeted coverage

module sva_priority_encoder(
  input logic [3:0] in1,
  input logic [3:0] in2,
  input logic [3:0] priority_output
);
  default clocking cb @($global_clock); endclocking

  let p = (in1 > in2) ? in1 : in2;

  // Functional correctness
  a_pe_func:  assert property (priority_output == p)
    else $error("priority_output mismatch");

  // No X/Z propagation when inputs are clean
  a_pe_no_x:  assert property (!$isunknown({in1,in2}) |-> !$isunknown(priority_output))
    else $error("priority_output has X/Z with clean inputs");

  // Coverage: all compare outcomes
  c_pe_gt:    cover property (in1 > in2);
  c_pe_lt:    cover property (in1 < in2);
  c_pe_eq:    cover property (in1 == in2);
endmodule


module sva_final_output_generator(
  input logic [3:0] in1,
  input logic [3:0] in2,
  input logic [3:0] priority_output,
  input logic [3:0] final_output
);
  default clocking cb @($global_clock); endclocking

  let p = (in1 > in2) ? in1 : in2;
  let f = (p==4'b0001) ? in1
        : (p==4'b0010) ? in2
        : (p==4'b0100) ? {in1[3:1], in2[0]}
        : (p==4'b1000) ? {in2[3:1], in1[0]}
        :                 4'b0000;

  // End-to-end functional correctness of final_output behavior
  a_fog_func: assert property (final_output == f)
    else $error("final_output mismatch");

  // No X/Z propagation when inputs are clean
  a_fog_no_x: assert property (!$isunknown({in1,in2}) |-> !$isunknown({priority_output,final_output}))
    else $error("priority_output/final_output has X/Z with clean inputs");

  // Coverage: hit each case item and default
  c_fog_case1:    cover property (p==4'b0001);
  c_fog_case2:    cover property (p==4'b0010);
  c_fog_case4:    cover property (p==4'b0100);
  c_fog_case8:    cover property (p==4'b1000);
  c_fog_default:  cover property (!(p inside {4'b0001,4'b0010,4'b0100,4'b1000}));
endmodule

// Bind assertions to DUTs
bind priority_encoder        sva_priority_encoder        pe_sva  (.*);
bind final_output_generator  sva_final_output_generator  fog_sva (.*);