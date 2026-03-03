// SVA checker for alu. Bind this to the DUT and provide a sampling clock.
// Example bind (replace tb_clk with your env clock):
// bind alu alu_sva u_alu_sva (.clk(tb_clk), .A(A), .B(B), .Op(Op), .result(result));

module alu_sva(
  input logic        clk,
  input logic [3:0]  A,
  input logic [3:0]  B,
  input logic [2:0]  Op,
  input logic [3:0]  result
);

  default clocking cb @(posedge clk); endclocking

  // Golden model (same ops as DUT, 4-bit truncation by type)
  function automatic logic [3:0] exp_val(input logic [3:0] a, b,
                                         input logic [2:0] op);
    case (op)
      3'b000: exp_val = a + b;    // add
      3'b001: exp_val = a - b;    // sub
      3'b010: exp_val = a & b;    // and
      3'b011: exp_val = a | b;    // or
      3'b100: exp_val = a ^ b;    // xor
      3'b101: exp_val = a << 1;   // shl
      3'b110: exp_val = a >> 1;   // shr
      3'b111: exp_val = a + 1;    // inc
      default: exp_val = a - 1;   // dec (only if Op has X/Z)
    endcase
  endfunction

  // No unknowns on control/data; prevents taking default via X/Z on Op
  ap_inputs_known: assert property ( !$isunknown({A,B,Op}) )
    else $error("ALU: X/Z on inputs A/B/Op");

  // If inputs known, output must be known
  ap_result_known: assert property ( (!$isunknown({A,B,Op})) |-> !$isunknown(result) )
    else $error("ALU: result has X/Z with known inputs");

  // Functional correctness for all opcodes (single concise golden check)
  ap_func_correct: assert property ( result == exp_val(A,B,Op) )
    else $error("ALU: result mismatch. Op=%0b A=%0h B=%0h res=%0h exp=%0h",
                Op, A, B, result, exp_val(A,B,Op));

  // Opcode coverage
  cp_op_add: cover property (Op == 3'b000);
  cp_op_sub: cover property (Op == 3'b001);
  cp_op_and: cover property (Op == 3'b010);
  cp_op_or : cover property (Op == 3'b011);
  cp_op_xor: cover property (Op == 3'b100);
  cp_op_shl: cover property (Op == 3'b101);
  cp_op_shr: cover property (Op == 3'b110);
  cp_op_inc: cover property (Op == 3'b111);

  // Corner-case coverage (wrap/borrow/bit-drops)
  cp_add_overflow: cover property (Op==3'b000 && ({1'b0,A}+{1'b0,B})[4]);
  cp_sub_borrow  : cover property (Op==3'b001 && (A < B));
  cp_shl_drop_msb: cover property (Op==3'b101 && A[3]);
  cp_shr_drop_lsb: cover property (Op==3'b110 && A[0]);
  cp_inc_wrap    : cover property (Op==3'b111 && A==4'hF);

  // Bitwise extremes (sanity)
  cp_and_zero: cover property (Op==3'b010 && (A & B)==4'h0);
  cp_or_full : cover property (Op==3'b011 && (A | B)==4'hF);
  cp_xor_zero: cover property (Op==3'b100 && (A ^ B)==4'h0);

endmodule