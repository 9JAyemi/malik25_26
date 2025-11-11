// SVA checker for top_module
module top_module_sva (
  input  logic [3:0] in,
  input  logic       out_and,
  input  logic       out_or,
  input  logic       out_xor,
  input  logic [7:0] final_out
);

  // Sample on any change of inputs (combinational)
  default clocking cb @(in); endclocking

  // Functional correctness of primary outputs
  property p_out_and; out_and == ((in[0] & in[1]) | (in[2] & in[3])); endproperty
  property p_out_or;  out_or  == ((in[0] | in[1]) & (in[2] | in[3])); endproperty
  property p_out_xor; out_xor == ((in[0] ^ in[1]) & (in[2] ^ in[3])); endproperty

  assert property(p_out_and) else $error("out_and != (in[0]&in[1])|(in[2]&in[3])");
  assert property(p_out_or)  else $error("out_or  != (in[0]|in[1])&(in[2]|in[3])");
  assert property(p_out_xor) else $error("out_xor != (in[0]^in[1])&(in[2]^in[3])");

  // Final output mapping and zero-extension
  property p_final_out_exact;
    final_out == {4'b0000, 1'b0, out_and, out_or, out_xor};
  endproperty
  assert property(p_final_out_exact) else $error("final_out mapping/zero-extension incorrect");

  // No X/Z on outputs when inputs are known
  property p_no_x_when_inputs_known;
    (!$isunknown(in)) |-> (!$isunknown({out_and, out_or, out_xor, final_out}));
  endproperty
  assert property(p_no_x_when_inputs_known) else $error("Outputs contain X/Z while inputs are known");

  // Toggle coverage on primary outputs
  cover property (@(posedge out_and) 1);
  cover property (@(negedge out_and) 1);
  cover property (@(posedge out_or)  1);
  cover property (@(negedge out_or)  1);
  cover property (@(posedge out_xor) 1);
  cover property (@(negedge out_xor) 1);

  // Value coverage: all input combinations, and all output combos reachable
  covergroup cg_in @(in);
    coverpoint in { bins all[] = {[0:15]}; }
  endgroup
  cg_in cg_in_i = new;

  covergroup cg_out @(in);
    coverpoint {out_and, out_or, out_xor} { bins all[] = {[0:7]}; }
  endgroup
  cg_out cg_out_i = new;

endmodule

// Bind into DUT
bind top_module top_module_sva sva_i (.*);