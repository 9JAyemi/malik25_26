// SVA checker for Arithmetic_Logic_Unit
module Arithmetic_Logic_Unit_sva (
  input  logic        clk,
  input  logic        rst_n,
  input  logic [4:0]  ctrl,
  input  logic [15:0] data_in_A,
  input  logic [15:0] data_in_B,
  input  logic [15:0] data_out
);

  // Golden model (matches DUT exactly)
  function automatic logic [15:0] alu_exp (input logic [4:0] c,
                                           input logic [15:0] a, b);
    unique case (c)
      5'd1 : alu_exp = a + b;
      5'd2 : alu_exp = a - b;
      5'd3 : alu_exp = a * b;
      5'd4 : alu_exp = a / b;
      5'd5 : alu_exp = a & b;
      5'd6 : alu_exp = a | b;
      5'd7 : alu_exp = a ^ b;
      5'd8 : alu_exp = ~a;
      5'd9 : alu_exp = a <<  b[3:0];
      5'd10: alu_exp = a >>  b[3:0];
      5'd11: alu_exp = a <<< b[3:0];
      5'd12: alu_exp = a >>> b[3:0];
      default: alu_exp = 16'h0000;
    endcase
  endfunction

  // Helpers
  function automatic bit known_inputs();
    return !$isunknown({ctrl, data_in_A, data_in_B});
  endfunction

  // Core functional equivalence (for all legal, fully-known cases)
  property p_result_matches_model;
    @(posedge clk) disable iff (!rst_n)
      known_inputs() && !(ctrl==5'd4 && data_in_B==16'd0)
      |-> data_out == alu_exp(ctrl, data_in_A, data_in_B);
  endproperty
  assert property (p_result_matches_model);

  // Default branch drives zero
  property p_default_zero;
    @(posedge clk) disable iff (!rst_n)
      ($isunknown(ctrl) || !(ctrl inside {[5'd1:5'd12]}))
      |-> data_out == 16'h0000;
  endproperty
  assert property (p_default_zero);

  // No X/Z on output for legal ops with known inputs
  property p_no_x_on_known_legal;
    @(posedge clk) disable iff (!rst_n)
      known_inputs() && (ctrl inside {[5'd1:5'd12]}) && !(ctrl==5'd4 && data_in_B==16'd0)
      |-> !$isunknown(data_out);
  endproperty
  assert property (p_no_x_on_known_legal);

  // Division by zero is illegal (DUT has no guard)
  property p_div_by_zero_illegal;
    @(posedge clk) disable iff (!rst_n)
      (ctrl==5'd4) |-> (data_in_B!=16'd0);
  endproperty
  assert property (p_div_by_zero_illegal);

  // Pure combinational: stable inputs -> stable output
  property p_stable_inputs_imply_stable_output;
    @(posedge clk) disable iff (!rst_n)
      $stable({ctrl, data_in_A, data_in_B}) |-> $stable(data_out);
  endproperty
  assert property (p_stable_inputs_imply_stable_output);

  // Shift ops depend only on low nibble of B
  property p_shift_upper_bits_irrelevant;
    @(posedge clk) disable iff (!rst_n)
      (ctrl inside {5'd9,5'd10,5'd11,5'd12}) &&
      (data_in_A == $past(data_in_A)) &&
      (data_in_B[3:0] == $past(data_in_B[3:0])) &&
      (data_in_B[15:4] != $past(data_in_B[15:4]))
      |-> data_out == $past(data_out);
  endproperty
  assert property (p_shift_upper_bits_irrelevant);

  // NOT op ignores B
  property p_not_ignores_B;
    @(posedge clk) disable iff (!rst_n)
      (ctrl==5'd8) && (data_in_A==$past(data_in_A)) && (data_in_B!=$past(data_in_B))
      |-> data_out == $past(data_out);
  endproperty
  assert property (p_not_ignores_B);

  // -----------------------
  // Functional coverage
  // -----------------------
  // Cover each opcode
  genvar i;
  generate
    for (i=1; i<=12; i++) begin : gen_cov_ops
      cover property (@(posedge clk) disable iff(!rst_n)
        known_inputs() && (ctrl == 5'(i)));
    end
  endgenerate

  // Cover default path
  cover property (@(posedge clk) disable iff(!rst_n)
    !(ctrl inside {[5'd1:5'd12]}));

  // Division: legal and illegal
  cover property (@(posedge clk) disable iff(!rst_n)
    known_inputs() && ctrl==5'd4 && (data_in_B!=16'd0));
  cover property (@(posedge clk) disable iff(!rst_n)
    known_inputs() && ctrl==5'd4 && (data_in_B==16'd0));

  // Shifts: amount 0 and 15
  cover property (@(posedge clk) disable iff(!rst_n)
    known_inputs() && (ctrl inside {5'd9,5'd10,5'd11,5'd12}) && data_in_B[3:0]==4'd0);
  cover property (@(posedge clk) disable iff(!rst_n)
    known_inputs() && (ctrl inside {5'd9,5'd10,5'd11,5'd12}) && data_in_B[3:0]==4'd15);

  // Multiply overflow observed (upper 16 bits nonzero)
  cover property (@(posedge clk) disable iff(!rst_n)
    known_inputs() && ctrl==5'd3 && (((data_in_A*data_in_B)>>16) != 0));

endmodule

// Example bind (connect any free-running clk/rst available in your environment):
// bind Arithmetic_Logic_Unit Arithmetic_Logic_Unit_sva u_alu_sva (.*, .clk(tb_clk), .rst_n(tb_rst_n));