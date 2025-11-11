// SVA for five_input_gate
module five_input_gate_sva (
  input logic in1, in2, in3, in4, in5,
  input logic out,
  input logic temp1, temp2
);
  default clocking cb @(posedge $global_clock); endclocking

  // Functional correctness with X-tolerance on inputs
  assert property ( !$isunknown({in1,in2})            |-> temp1 == (in1 & in2) );
  assert property ( !$isunknown({in3,in4})            |-> temp2 == (in3 & in4) );
  assert property ( !$isunknown({in1,in2,in3,in4,in5})|-> out   == ((in1 & in2) | (in3 & in4) | in5) );
  assert property ( !$isunknown({in1,in2,in3,in4,in5})|-> !$isunknown(out) );

  // Key functional coverage (each cone and corner cases)
  cover property ( !$isunknown({in1,in2,in3,in4,in5}) && !in5 && (in1 & in2) && !(in3 & in4) &&  out );
  cover property ( !$isunknown({in1,in2,in3,in4,in5}) && !in5 && !(in1 & in2) && (in3 & in4) &&  out );
  cover property ( !$isunknown({in1,in2,in3,in4,in5}) &&  in5 && !(in1 & in2) && !(in3 & in4) &&  out );
  cover property ( !$isunknown({in1,in2,in3,in4,in5}) && !(in1 & in2) && !(in3 & in4) && !in5 && !out );
  cover property ( !$isunknown({in1,in2,in3,in4,in5}) &&  (in1 & in2) &&  (in3 & in4) && out );

  // Full 5-input space coverage (concise)
  covergroup cg_inputs @(cb);
    option.per_instance = 1;
    coverpoint {in5,in4,in3,in2,in1} { bins all[] = {[0:31]}; }
  endgroup
  cg_inputs cg = new();

endmodule

// Bind into DUT to observe internals temp1/temp2
bind five_input_gate five_input_gate_sva five_input_gate_sva_i (.*);