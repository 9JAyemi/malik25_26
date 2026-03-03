// SVA checker for alu
// Assumes a free-running clk and active-low reset are available in the environment.
// Bind this checker to the DUT instance.
module alu_sva (
  input logic        clk,
  input logic        reset_n,

  // DUT ports
  input  logic [3:0] A,
  input  logic [3:0] B,
  input  logic [2:0] opcode,
  input  logic       carry_in,
  input  logic       invert,
  input  logic [3:0] result,
  input  logic       carry_out
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (!reset_n);

  // Golden-model computation
  logic [4:0] add5;
  logic [4:0] sub5;        // A - B - carry_in modeled as A + ~B + (1 - carry_in)
  logic [3:0] core_res;    // pre-invert result per opcode
  logic       core_cout;   // carry/borrow per opcode (no invert effect)
  logic [3:0] exp_result;  // post-invert expected result
  logic       exp_cout;

  always_comb begin
    add5 = {1'b0, A} + {1'b0, B} + {4'b0, carry_in};
    sub5 = {1'b0, A} + {1'b0, ~B} + {4'b0, ~carry_in}; // + (1 - carry_in)

    unique case (opcode)
      3'b000: begin // ADD
        core_res  = add5[3:0];
        core_cout = add5[4];
      end
      3'b001: begin // SUB with borrow_in = carry_in
        core_res  = sub5[3:0];     // low 4-bit difference
        core_cout = ~sub5[4];      // borrow_out = 1 when no final carry
      end
      3'b010: begin core_res = (A & B); core_cout = 1'b0; end
      3'b011: begin core_res = (A | B); core_cout = 1'b0; end
      3'b100: begin core_res = (A ^ B); core_cout = 1'b0; end
      default: begin core_res = 4'b0000; core_cout = 1'b0; end
    endcase

    exp_result = invert ? ~core_res : core_res;
    exp_cout   = core_cout;
  end

  // Functional correctness
  property p_result_correct; result == exp_result; endproperty
  property p_cout_correct;   carry_out == exp_cout; endproperty

  // Bitwise ops must never raise carry_out
  property p_bitwise_cout_zero;
    (opcode inside {3'b010,3'b011,3'b100,3'b101,3'b110,3'b111}) |-> (carry_out == 1'b0);
  endproperty

  // Default opcodes produce zero (or all-ones if inverted)
  property p_default_result;
    (opcode inside {3'b101,3'b110,3'b111}) |->
      (result == (invert ? 4'hF : 4'h0));
  endproperty

  // Invert only affects result, not carry_out
  property p_invert_only_affects_result;
    $changed(invert) |-> $stable(carry_out);
  endproperty

  assert property (p_result_correct);
  assert property (p_cout_correct);
  assert property (p_bitwise_cout_zero);
  assert property (p_default_result);
  assert property (p_invert_only_affects_result);

  // Minimal but meaningful functional coverage
  cover property (opcode == 3'b000); // ADD
  cover property (opcode == 3'b001); // SUB
  cover property (opcode == 3'b010); // AND
  cover property (opcode == 3'b011); // OR
  cover property (opcode == 3'b100); // XOR
  cover property (opcode inside {3'b101,3'b110,3'b111}); // DEFAULT

  cover property ((opcode == 3'b000) && (exp_cout == 1'b1)); // ADD carry
  cover property ((opcode == 3'b000) && (exp_cout == 1'b0)); // ADD no carry
  cover property ((opcode == 3'b001) && (exp_cout == 1'b1)); // SUB borrow
  cover property ((opcode == 3'b001) && (exp_cout == 1'b0)); // SUB no borrow

  cover property (invert == 1'b0);
  cover property (invert == 1'b1);

  // Some extreme bitwise results
  cover property ((opcode == 3'b010) && (result == 4'h0)); // AND -> 0
  cover property ((opcode == 3'b011) && (result == 4'hF)); // OR -> F
  cover property ((opcode == 3'b100) && (result == 4'hF)); // XOR -> F
endmodule

// Example bind (edit clk/reset_n paths for your environment):
// bind alu alu_sva u_alu_sva (.* , .clk(tb_clk), .reset_n(tb_reset_n));