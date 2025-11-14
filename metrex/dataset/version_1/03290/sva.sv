// SVA for top_module, alu_32bit, and adder_subtractor_8bit
// Bind examples (adjust clk as appropriate):
//   bind top_module                 top_module_sva              u_top_sva(.clk(clk));
//   bind alu_32bit                  alu_32bit_sva               u_alu_sva(.clk(clk));
//   bind adder_subtractor_8bit      adder_subtractor_8bit_sva   u_addsub_sva(.clk(clk));

module top_module_sva(input logic clk);
  default clocking @(posedge clk); endclocking

  // Basic X checks
  a_inputs_known:  assert property (!$isunknown({a,b,ctrl}));
  a_outputs_known: assert property (!$isunknown({result,overflow}));

  // Structural/functional checks
  a_mask_hi_zero:  assert property (result[31:8] == 24'h0);
  a_and_low8:      assert property (result[7:0] == (alu_output[7:0] & adder_output));
  a_ovf_passthru:  assert property (overflow == overflow_adder);

  // If inputs known, internal wires should be known
  a_known_path:    assert property (!$isunknown({a,b,ctrl}) |-> !$isunknown({alu_output,adder_output,overflow_adder}));

  // Functional coverage
  c_alu_ops:       cover property (ctrl[3:0] inside {4'h0,4'h1,4'h2,4'h3,4'h4,4'h5,4'h6});
  c_alu_default:   cover property (ctrl[3:0] inside {[4'h7:4'hF]});
  c_add_mode:      cover property (ctrl[7]==1'b0);
  c_sub_mode:      cover property (ctrl[7]==1'b1);
  c_add_overflow:  cover property (ctrl[7]==1'b0 && overflow);
  c_sub_overflow:  cover property (ctrl[7]==1'b1 && overflow);
endmodule

module alu_32bit_sva(input logic clk);
  default clocking @(posedge clk); endclocking

  a_inputs_known: assert property (!$isunknown({a,b,ctrl}));
  a_outputs_known: assert property (!$isunknown(result));

  // Opcode checks
  a_add:      assert property (ctrl==4'h0 |-> result == a + b);
  a_sub:      assert property (ctrl==4'h1 |-> result == a - b);
  a_and:      assert property (ctrl==4'h2 |-> result == (a & b));
  a_or:       assert property (ctrl==4'h3 |-> result == (a | b));
  a_xor:      assert property (ctrl==4'h4 |-> result == (a ^ b));
  a_sll1:     assert property (ctrl==4'h5 |-> result == (a << 1));
  a_srl1:     assert property (ctrl==4'h6 |-> result == (a >> 1));
  a_default0: assert property (ctrl inside {[4'h7:4'hF]} |-> result == 32'h0);

  // Coverage of each opcode and default
  c_op0: cover property (ctrl==4'h0);
  c_op1: cover property (ctrl==4'h1);
  c_op2: cover property (ctrl==4'h2);
  c_op3: cover property (ctrl==4'h3);
  c_op4: cover property (ctrl==4'h4);
  c_op5: cover property (ctrl==4'h5);
  c_op6: cover property (ctrl==4'h6);
  c_op_def: cover property (ctrl inside {[4'h7:4'hF]});
endmodule

module adder_subtractor_8bit_sva(input logic clk);
  default clocking @(posedge clk); endclocking

  // X checks
  a_inputs_known:  assert property (!$isunknown({a,b,ctrl}));
  a_outputs_known: assert property (!$isunknown({result,overflow}));

  // Result correctness
  a_add_res: assert property (!ctrl |-> result == (a + b));
  a_sub_res: assert property ( ctrl |-> result == (a - b));

  // Independent signed-overflow check via carry into/out of MSB
  let add9 = {1'b0,a} + {1'b0,b};
  let sub9 = {1'b0,a} + {1'b0,~b} + 9'd1;

  a_add_ovf: assert property (!ctrl |-> overflow == (add9[8] ^ add9[7]));
  a_sub_ovf: assert property ( ctrl |-> overflow == (sub9[8] ^ sub9[7]));

  // Coverage
  c_add:      cover property (!ctrl);
  c_sub:      cover property ( ctrl);
  c_add_ovf:  cover property (!ctrl && overflow);
  c_sub_ovf:  cover property ( ctrl && overflow);
endmodule