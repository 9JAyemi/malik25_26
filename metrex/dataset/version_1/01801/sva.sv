// SVA for multiplier_alu_top design
package mul_alu_sva_pkg;
  // Low 8-bit multiply model
  function automatic [7:0] f_mul_lo8(input [7:0] a, input [7:0] b);
    return (a * b)[7:0];
  endfunction

  // 4-bit ALU model (truncated to 4 bits)
  function automatic [3:0] f_alu4(input [3:0] a, input [3:0] b, input [2:0] op);
    case (op)
      3'b000: f_alu4 = (a + b) & 4'hF;
      3'b001: f_alu4 = (a - b) & 4'hF;
      3'b010: f_alu4 = (a & b);
      3'b011: f_alu4 = (a | b);
      3'b100: f_alu4 = (a ^ b);
      3'b101: f_alu4 = (a << 1) & 4'hF;
      default: f_alu4 = 4'h0;
    endcase
  endfunction
endpackage


// Top-level SVA (uses only DUT ports)
module multiplier_alu_top_sva
(
  input  [7:0] A,
  input  [7:0] B,
  input  [2:0] OP,
  input  [7:0] final_output
);
  import mul_alu_sva_pkg::*;

  // Expected top-level result (mult upper byte is 0; final_output is zero-extended ALU result)
  function automatic [7:0] exp_final(input [7:0] A, input [7:0] B, input [2:0] OP);
    automatic [3:0] a4 = f_mul_lo8(A,B)[7:4];
    automatic [3:0] b4 = A[3:0];
    exp_final = {4'h0, f_alu4(a4, b4, OP)};
  endfunction

  // Functional equivalence
  property p_top_eq;
    !$isunknown({A,B,OP}) |-> (final_output == exp_final(A,B,OP));
  endproperty
  assert property (@(A or B or OP) p_top_eq)
    else $error("multiplier_alu_top: final_output mismatch");

  // Upper nibble must always be 0
  assert property (@(A or B or OP) !$isunknown({A,B,OP}) |-> (final_output[7:4] == 4'h0))
    else $error("multiplier_alu_top: final_output[7:4] not zero");

  // Coverage: exercise ALU ops and datapath usage
  cover property (@(A or B or OP) (OP==3'b000));
  cover property (@(A or B or OP) (OP==3'b001));
  cover property (@(A or B or OP) (OP==3'b010));
  cover property (@(A or B or OP) (OP==3'b011));
  cover property (@(A or B or OP) (OP==3'b100));
  cover property (@(A or B or OP) (OP==3'b101));
  cover property (@(A or B or OP) (OP==3'b110));
  cover property (@(A or B or OP) (OP==3'b111));
  // Ensure ALU A input path (mult_result[7:4]) is exercised
  cover property (@(A or B) (f_mul_lo8(A,B)[7:4] != 4'h0));
endmodule


// Multiplier SVA
module multiplier_8bit_sva
(
  input  [7:0]  A,
  input  [7:0]  B,
  input  [15:0] P
);
  import mul_alu_sva_pkg::*;

  // Upper half must be zero by design
  assert property (@(A or B) !$isunknown({A,B}) |-> (P[15:8] == 8'h00))
    else $error("multiplier_8bit: P[15:8] not zero");

  // Low 8 bits must match (A*B)[7:0]
  assert property (@(A or B) !$isunknown({A,B}) |-> (P[7:0] == f_mul_lo8(A,B)))
    else $error("multiplier_8bit: P[7:0] != (A*B)[7:0]");

  // No X-propagation when inputs known
  assert property (@(A or B) !$isunknown({A,B}) |-> !$isunknown(P))
    else $error("multiplier_8bit: X/Z on P with known inputs");

  // Coverage: key multiplier scenarios
  cover property (@(A or B) (A==8'h00));
  cover property (@(A or B) (B==8'h00));
  cover property (@(A or B) (A==8'hFF && B==8'hFF));
  // Each single-bit B selects the shifted A contribution (modulo 8 bits)
  genvar i;
  generate
    for (i=0; i<8; i++) begin : g_cov_pp
      cover property (@(A or B) (B == (8'h1 << i)) && (P[7:0] == ((A << i) & 8'hFF)));
    end
  endgenerate
endmodule


// 4-bit ALU SVA
module alu_4bit_sva
(
  input  [3:0] A,
  input  [3:0] B,
  input  [2:0] OP,
  input  [3:0] Y
);
  import mul_alu_sva_pkg::*;

  // Functional equivalence to model
  assert property (@(A or B or OP) !$isunknown({A,B,OP}) |-> (Y == f_alu4(A,B,OP)))
    else $error("alu_4bit: Y mismatch");

  // No X-propagation when inputs known
  assert property (@(A or B or OP) !$isunknown({A,B,OP}) |-> !$isunknown(Y))
    else $error("alu_4bit: X/Z on Y with known inputs");

  // Coverage: opcodes and corner cases
  cover property (@(A or B or OP) (OP==3'b000)); // add
  cover property (@(A or B or OP) (OP==3'b001)); // sub
  cover property (@(A or B or OP) (OP==3'b010)); // and
  cover property (@(A or B or OP) (OP==3'b011)); // or
  cover property (@(A or B or OP) (OP==3'b100)); // xor
  cover property (@(A or B or OP) (OP==3'b101)); // shl
  cover property (@(A or B or OP) (OP==3'b110)); // default->0
  cover property (@(A or B or OP) (OP==3'b111)); // default->0

  // Add overflow (truncation)
  cover property (@(A or B or OP) (OP==3'b000) && ((A + B) > 4'hF));
  // Sub borrow (underflow)
  cover property (@(A or B or OP) (OP==3'b001) && (A < B));
  // Shift out MSB
  cover property (@(A or B or OP) (OP==3'b101) && A[3]);
endmodule


// Bind SVA to DUT
bind multiplier_alu_top  multiplier_alu_top_sva u_multiplier_alu_top_sva (.*);
bind multiplier_8bit     multiplier_8bit_sva    u_multiplier_8bit_sva (.*);
bind alu_4bit            alu_4bit_sva           u_alu_4bit_sva (.*);