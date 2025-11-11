// SVA for top_module/alu/twos_complement
module top_module_sva (
  input logic        clk,
  input logic        reset,
  input logic [3:0]  a,
  input logic [3:0]  b,
  input logic [2:0]  op,
  input logic [3:0]  q,
  input logic [3:0]  alu_output
);
  default clocking cb @(posedge clk); endclocking

  // Helper expressions
  let add_e = (a + b) & 4'hF;
  let sub_e = (a - b) & 4'hF;
  let and_e = a & b;
  let or_e  = a | b;
  let xor_e = a ^ b;
  let shl_e = {a[2:0],1'b0};
  let tc_e  = (~alu_output + 4'd1) & 4'hF;

  // No-X on outputs when inputs are known
  assert property (disable iff (reset) (!$isunknown({a,b,op})) |-> (!$isunknown({alu_output,q})));

  // ALU functional checks
  assert property (disable iff (reset) (op==3'b000) |-> (alu_output==add_e));
  assert property (disable iff (reset) (op==3'b001) |-> (alu_output==sub_e));
  assert property (disable iff (reset) (op==3'b010) |-> (alu_output==and_e));
  assert property (disable iff (reset) (op==3'b011) |-> (alu_output==or_e));
  assert property (disable iff (reset) (op==3'b100) |-> (alu_output==xor_e));
  assert property (disable iff (reset) (op==3'b101) |-> (alu_output==shl_e));
  assert property (disable iff (reset) (op inside {3'b110,3'b111}) |-> (alu_output==4'h0));

  // Two's complement block check
  assert property (disable iff (reset) (q == tc_e));

  // Integration consistency (redundant but strong)
  assert property (disable iff (reset) (((alu_output + q) & 4'hF) == 4'h0));

  // Functional coverage
  cover property (disable iff (reset) (op==3'b000));
  cover property (disable iff (reset) (op==3'b001));
  cover property (disable iff (reset) (op==3'b010));
  cover property (disable iff (reset) (op==3'b011));
  cover property (disable iff (reset) (op==3'b100));
  cover property (disable iff (reset) (op==3'b101));
  cover property (disable iff (reset) (op inside {3'b110,3'b111}));

  // Corner-case coverage
  cover property (disable iff (reset) (op==3'b000 && ({1'b0,a}+{1'b0,b})[4])); // add carry-out
  cover property (disable iff (reset) (op==3'b001 && (a < b)));                // sub borrow
  cover property (disable iff (reset) (op==3'b101 && a[3]));                   // shift-out MSB
  cover property (disable iff (reset) (a==4'h0 && b==4'h0));
  cover property (disable iff (reset) (a==4'hF || b==4'hF));
endmodule

// Bind to DUT; exposes internal alu_output for checking
bind top_module top_module_sva u_top_module_sva (
  .clk        (clk),
  .reset      (reset),
  .a          (a),
  .b          (b),
  .op         (op),
  .q          (q),
  .alu_output (alu_output)
);