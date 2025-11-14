// SVA for top_module, covering nor_logic and control_logic behavior.
// Assumes a free-running sample clock `clk` from the TB.

module top_module_sva #(parameter W=4) (
  input  logic                 clk,
  input  logic [W-1:0]         in,
  input  logic                 select,
  input  logic                 out_and,
  input  logic                 out_or,
  input  logic                 out_xor,
  input  logic [1:0]           active_output,
  // tap internal nets from top_module
  input  logic                 out_and_nor,
  input  logic                 out_or_nor,
  input  logic                 out_xor_nor
);
  default clocking cb @(posedge clk); endclocking

  // Control logic mapping and onehot set
  a_ctrl_map0: assert property (select==1'b0 |-> active_output==2'b10);
  a_ctrl_map1: assert property (select==1'b1 |-> active_output==2'b01);
  a_ctrl_onehot: assert property (active_output inside {2'b10,2'b01});

  // NOR submodule functional correctness (independent of selection)
  a_nor_and:  assert property (out_and_nor ==  (&in));
  a_nor_or:   assert property (out_or_nor  == ~(|in));
  a_nor_xor3: assert property (out_xor_nor === ~(in[0]^~in[0]^in[1]^~in[1]^in[2]^~in[2]^in[3]^~in[3]));
  a_nor_xor_known: assert property (!$isunknown(in) |-> out_xor_nor==1'b1);

  // Output selection/gating correctness
  a_sel_left : assert property (active_output==2'b10 |->
                                (out_and==out_and_nor && out_or==1'b0 && out_xor==1'b0));
  a_sel_right: assert property (active_output==2'b01 |->
                                (out_and==1'b0 && out_or==out_or_nor && out_xor==out_xor_nor));

  // End-to-end: outputs are fully determined and 2-state when inputs are 2-state
  a_known_outs: assert property (!$isunknown({in,select}) |->
                                 !$isunknown({out_and,out_or,out_xor,active_output}));

  // Compact functional end-to-end (helps catch any unintended wiring)
  a_e2e_and: assert property (out_and == ((active_output==2'b10) ? (&in)      : 1'b0));
  a_e2e_or : assert property (out_or  == ((active_output==2'b01) ? ~(|in)     : 1'b0));
  a_e2e_xor: assert property (out_xor === ((active_output==2'b01) ? 
                                           ~(in[0]^~in[0]^in[1]^~in[1]^in[2]^~in[2]^in[3]^~in[3]) : 1'b0));
  a_e2e_xor_known: assert property (!$isunknown(in) && active_output==2'b01 |-> out_xor==1'b1);

  // Minimal but meaningful coverage
  c_sel0:     cover property (active_output==2'b10);
  c_sel1:     cover property (active_output==2'b01);
  c_and1:     cover property (active_output==2'b10 && in=={W{1'b1}} && out_and);
  c_or1:      cover property (active_output==2'b01 && in=={W{1'b0}} && out_or);
  c_mixed:    cover property (active_output==2'b01 && (|in) && (~&in) && out_xor);
endmodule

// Example bind (from your testbench/top), providing a sampling clock `clk`:
// bind top_module top_module_sva u_top_sva (
//   .clk(tb.clk),
//   .in(in), .select(select),
//   .out_and(out_and), .out_or(out_or), .out_xor(out_xor),
//   .active_output(active_output),
//   .out_and_nor(out_and_nor), .out_or_nor(out_or_nor), .out_xor_nor(out_xor_nor)
// );