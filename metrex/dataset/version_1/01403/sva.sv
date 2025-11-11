// SVA for module pipeline
module pipeline_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic [15:0] instruction,
  input  logic [2:0]  reg1_addr,
  input  logic [2:0]  reg2_addr,
  input  logic [2:0]  reg3_addr,
  input  logic [15:0] reg1_data,
  input  logic [15:0] reg2_data,
  input  logic [15:0] reg3_data,
  input  logic [15:0] reg1_out,
  input  logic [15:0] reg2_out,
  input  logic [15:0] reg3_out,
  input  logic [15:0] inst1, inst2, inst3,
  input  logic [2:0]  reg1_addr1, reg2_addr1, reg3_addr1,
  input  logic [2:0]  reg1_addr2, reg2_addr2, reg3_addr2,
  input  logic [2:0]  reg1_addr3, reg2_addr3, reg3_addr3,
  input  logic [15:0] reg1_data1, reg2_data1, reg3_data1,
  input  logic [15:0] reg1_data2, reg2_data2, reg3_data2,
  input  logic [15:0] reg1_data3, reg2_data3, reg3_data3
);
  default clocking cb @(posedge clk); endclocking

  localparam logic [2:0] OP_ADD=3'b000, OP_SUB=3'b001, OP_AND=3'b010, OP_OR=3'b011, OP_XOR=3'b100;

  function automatic logic [15:0] alu(input logic [2:0] op, input logic [15:0] a, b);
    case (op)
      OP_ADD: alu = a + b;
      OP_SUB: alu = a - b;
      OP_AND: alu = a & b;
      OP_OR : alu = a | b;
      OP_XOR: alu = a ^ b;
      default: alu = 'x;
    endcase
  endfunction

  // Reset behavior
  assert property (reset |-> (inst1==0 && inst2==0 && inst3==0
                           && reg1_addr1==0 && reg2_addr1==0 && reg3_addr1==0
                           && reg1_data1==0 && reg2_data1==0 && reg3_data1==0
                           && reg1_addr2==0 && reg2_addr2==0 && reg3_addr2==0
                           && reg1_data2==0 && reg2_data2==0 && reg3_data2==0
                           && reg1_addr3==0 && reg2_addr3==0 && reg3_addr3==0
                           && reg1_data3==0 && reg2_data3==0 && reg3_data3==0));
  assert property (reset |-> $stable({reg1_out,reg2_out,reg3_out}));

  // Pipeline shift: instructions
  assert property (!reset |-> inst1 == $past(instruction));
  assert property (!reset |-> inst2 == $past(inst1));
  assert property (!reset |-> inst3 == $past(inst2));

  // Pipeline shift: addresses
  assert property (!reset |-> reg1_addr1 == $past(reg1_addr));
  assert property (!reset |-> reg2_addr1 == $past(reg2_addr));
  assert property (!reset |-> reg3_addr1 == $past(reg3_addr));
  assert property (!reset |-> reg1_addr2 == $past(reg1_addr1));
  assert property (!reset |-> reg2_addr2 == $past(reg2_addr1));
  assert property (!reset |-> reg3_addr2 == $past(reg3_addr1));
  assert property (!reset |-> reg1_addr3 == $past(reg1_addr2));
  assert property (!reset |-> reg2_addr3 == $past(reg2_addr2));
  assert property (!reset |-> reg3_addr3 == $past(reg3_addr2));

  // Pipeline shift: data
  assert property (!reset |-> reg1_data1 == $past(reg1_data));
  assert property (!reset |-> reg2_data1 == $past(reg2_data));
  assert property (!reset |-> reg3_data1 == $past(reg3_data));
  assert property (!reset |-> reg1_data2 == $past(reg1_data1));
  assert property (!reset |-> reg2_data2 == $past(reg2_data1));
  assert property (!reset |-> reg3_data2 == $past(reg3_data1));
  assert property (!reset |-> reg1_data3 == $past(reg1_data2));
  assert property (!reset |-> reg2_data3 == $past(reg2_data2));
  assert property (!reset |-> reg3_data3 == $past(reg3_data2));

  // Functional correctness of outputs (active opcodes)
  property op3_active; (inst3[15:13] inside {OP_ADD,OP_SUB,OP_AND,OP_OR,OP_XOR}) &&
                       !$isunknown({inst3[15:13],reg1_data3,reg2_data3}); endproperty
  assert property (op3_active |-> reg1_out == alu(inst3[15:13], reg1_data3, reg2_data3));
  assert property ((inst3[15:13] inside {[3'b101:3'b111]}) |-> $stable(reg1_out));

  property op2_active; (inst2[15:13] inside {OP_ADD,OP_SUB,OP_AND,OP_OR,OP_XOR}) &&
                       !$isunknown({inst2[15:13],reg2_data3,reg3_data3}); endproperty
  assert property (op2_active |-> reg2_out == alu(inst2[15:13], reg2_data3, reg3_data3));
  assert property ((inst2[15:13] inside {[3'b101:3'b111]}) |-> $stable(reg2_out));

  property op1_active; (inst1[15:13] inside {OP_ADD,OP_SUB,OP_AND,OP_OR,OP_XOR}) &&
                       !$isunknown({inst1[15:13],reg3_data3,reg1_data3}); endproperty
  assert property (op1_active |-> reg3_out == alu(inst1[15:13], reg3_data3, reg1_data3));
  assert property ((inst1[15:13] inside {[3'b101:3'b111]}) |-> $stable(reg3_out));

  // End-to-end latency checks vs inputs
  assert property (!reset && (instruction[15:13] inside {OP_ADD,OP_SUB,OP_AND,OP_OR,OP_XOR})
                   |-> ##3 reg1_out == alu($past(instruction,3)[15:13],
                                           $past(reg1_data,3), $past(reg2_data,3)));
  assert property (!reset && (instruction[15:13] inside {OP_ADD,OP_SUB,OP_AND,OP_OR,OP_XOR})
                   |-> ##2 reg2_out == alu($past(instruction,2)[15:13],
                                           $past(reg2_data,3), $past(reg3_data,3)));
  assert property (!reset && (instruction[15:13] inside {OP_ADD,OP_SUB,OP_AND,OP_OR,OP_XOR})
                   |-> ##1 reg3_out == alu($past(instruction,1)[15:13],
                                           $past(reg3_data,3), $past(reg1_data,3)));

  // Sanity: no X on opcode fields when pipeline active
  assert property (!reset |-> !$isunknown(inst1[15:13]));
  assert property (!reset |-> !$isunknown(inst2[15:13]));
  assert property (!reset |-> !$isunknown(inst3[15:13]));

  // Coverage
  cover property (!reset and (inst3[15:13] inside {OP_ADD,OP_SUB,OP_AND,OP_OR,OP_XOR}));
  cover property (!reset and (inst2[15:13] inside {OP_ADD,OP_SUB,OP_AND,OP_OR,OP_XOR}));
  cover property (!reset and (inst1[15:13] inside {OP_ADD,OP_SUB,OP_AND,OP_OR,OP_XOR}));
  cover property (!reset and (instruction[15:13]==OP_ADD) ##1 (instruction[15:13]==OP_SUB)
                         ##1 (instruction[15:13]==OP_AND) ##1 (instruction[15:13]==OP_OR)
                         ##1 (instruction[15:13]==OP_XOR));
endmodule

bind pipeline pipeline_sva
(
  .clk(clk), .reset(reset),
  .instruction(instruction),
  .reg1_addr(reg1_addr), .reg2_addr(reg2_addr), .reg3_addr(reg3_addr),
  .reg1_data(reg1_data), .reg2_data(reg2_data), .reg3_data(reg3_data),
  .reg1_out(reg1_out), .reg2_out(reg2_out), .reg3_out(reg3_out),
  .inst1(inst1), .inst2(inst2), .inst3(inst3),
  .reg1_addr1(reg1_addr1), .reg2_addr1(reg2_addr1), .reg3_addr1(reg3_addr1),
  .reg1_addr2(reg1_addr2), .reg2_addr2(reg2_addr2), .reg3_addr2(reg3_addr2),
  .reg1_addr3(reg1_addr3), .reg2_addr3(reg2_addr3), .reg3_addr3(reg3_addr3),
  .reg1_data1(reg1_data1), .reg2_data1(reg2_data1), .reg3_data1(reg3_data1),
  .reg1_data2(reg1_data2), .reg2_data2(reg2_data2), .reg3_data2(reg3_data2),
  .reg1_data3(reg1_data3), .reg2_data3(reg2_data3), .reg3_data3(reg3_data3)
);