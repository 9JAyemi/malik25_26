// SVA checker for ALU; bind this to your DUT. Provide a clock from TB.
// Example bind:
//   bind ALU alu_sva #(.N(N)) u_alu_sva (.* , .clk(tb_clk));
checker alu_sva #(parameter int N=32)
(
  input logic                  clk,
  input logic [3:0]            op_code,
  input logic signed [N-1:0]   operand1,
  input logic signed [N-1:0]   operand2,
  input logic signed [N-1:0]   result,
  input logic                  zero,
  input logic                  overflow
);
  default clocking cb @(posedge clk); endclocking

  // Basic sanity
  assert property (!$isunknown({op_code,operand1,operand2})) else $error("Inputs contain X/Z");
  assert property (!$isunknown({result,zero,overflow}))      else $error("Outputs contain X/Z");

  // Zero flag correctness
  assert property (zero == (result == '0))
    else $error("Zero flag mismatch");

  // Default/illegal opcode behavior
  assert property ((op_code > 4'd9) |-> (result == '0 && overflow == 1'b0))
    else $error("Default case mismatch");

  // Per-op functional checks (match DUT behavior exactly)
  // 0: logical left shift
  assert property ((op_code==4'd0) |-> ({overflow,result} == {1'b0, (operand2 <<  operand1[4:0])}))
    else $error("LLS mismatch");
  // 1: logical right shift
  assert property ((op_code==4'd1) |-> ({overflow,result} == {1'b0, (operand2 >>  operand1[4:0])}))
    else $error("LRS mismatch");
  // 2: arithmetic right shift
  assert property ((op_code==4'd2) |-> ({overflow,result} == {1'b0, (operand2 >>> operand1[4:0])}))
    else $error("ARS mismatch");
  // 3: addition (overflow bit is carry-out of N-bit add)
  assert property ((op_code==4'd3) |-> ({overflow,result} == (operand1 + operand2)))
    else $error("ADD mismatch");
  // 4: subtraction (overflow bit is borrow/carry-out of N-bit sub)
  assert property ((op_code==4'd4) |-> ({overflow,result} == (operand1 - operand2)))
    else $error("SUB mismatch");
  // 5: AND
  assert property ((op_code==4'd5) |-> ({overflow,result} == {1'b0, (operand1 & operand2)}))
    else $error("AND mismatch");
  // 6: OR
  assert property ((op_code==4'd6) |-> ({overflow,result} == {1'b0, (operand1 | operand2)}))
    else $error("OR mismatch");
  // 7: XOR
  assert property ((op_code==4'd7) |-> ({overflow,result} == {1'b0, (operand1 ^ operand2)}))
    else $error("XOR mismatch");
  // 8: NOR
  assert property ((op_code==4'd8) |-> ({overflow,result} == {1'b0, ~(operand1 | operand2)}))
    else $error("NOR mismatch");
  // 9: signed less-than; result is N-bit with only bit0 set when true, overflow=0
  assert property ((op_code==4'd9) |-> ({overflow,result} == {1'b0, {{N-1{1'b0}}, (operand1 < operand2)}}))
    else $error("SLT mismatch");

  // Coverage: opcodes, flags, corner cases
  cover property (op_code==4'd0);
  cover property (op_code==4'd1);
  cover property (op_code==4'd2);
  cover property (op_code==4'd3);
  cover property (op_code==4'd4);
  cover property (op_code==4'd5);
  cover property (op_code==4'd6);
  cover property (op_code==4'd7);
  cover property (op_code==4'd8);
  cover property (op_code==4'd9);
  cover property (op_code>4'd9);

  // Zero flag both ways
  cover property (zero && (result=='0));
  cover property (!zero && (result!='0));

  // Shifts: amount 0 and max 31
  cover property ((op_code inside {4'd0,4'd1,4'd2}) && (operand1[4:0]==5'd0));
  cover property ((op_code inside {4'd0,4'd1,4'd2}) && (operand1[4:0]==5'd31));

  // ARS with negative operand2
  cover property ((op_code==4'd2) && operand2[N-1]);

  // ADD/SUB overflow (carry-out) asserted and deasserted
  cover property ((op_code==4'd3) && overflow);
  cover property ((op_code==4'd3) && !overflow);
  cover property ((op_code==4'd4) && overflow);
  cover property ((op_code==4'd4) && !overflow);

  // SLT true/false
  cover property ((op_code==4'd9) && (result=={{N-1{1'b0}},1'b1}));
  cover property ((op_code==4'd9) && (result=='0));
endchecker