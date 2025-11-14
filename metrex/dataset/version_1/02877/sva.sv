// SVA checker for calculator
// Bind example: bind calculator calculator_sva u_calculator_sva(.clk(clk), .rst_n(rst_n));

module calculator_sva(input logic clk, input logic rst_n);
  // Accesses bound instance signals: a, b, op, result

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  // Expected (as-implemented) combinational result (8-bit)
  function automatic logic [7:0] exp_result(input logic [7:0] a_i,
                                            input logic [7:0] b_i,
                                            input logic [1:0] op_i);
    logic [15:0] prod;
    case (op_i)
      2'b00: exp_result = (a_i + b_i) & 8'hFF;        // add (mod 256)
      2'b01: exp_result = (a_i - b_i) & 8'hFF;        // sub (mod 256)
      2'b10: begin prod = a_i * b_i; exp_result = prod[7:0]; end // mul (mod 256)
      2'b11: exp_result = (b_i == 0) ? 8'h00 : (a_i % b_i);      // only remainder fits in 8b
      default: exp_result = 'x;
    endcase
  endfunction

  // Functional correctness (as implemented)
  ap_func:  assert property (result == exp_result(a, b, op));

  // Operation-specific checks (masking ensures 8-bit wrap behavior)
  ap_add:   assert property ((op == 2'b00) |-> (result == ((a + b) & 8'hFF)));
  ap_sub:   assert property ((op == 2'b01) |-> (result == ((a - b) & 8'hFF)));
  ap_mul:   assert property ((op == 2'b10) |-> (result == ((a * b) & 8'hFF)));
  ap_div0:  assert property ((op == 2'b11 && b == 8'h00) |-> (result == 8'h00));
  ap_divnz: assert property ((op == 2'b11 && b != 8'h00) |-> (result == (a % b)));

  // X/Z propagation: clean inputs imply clean output
  ap_no_x:  assert property (!$isunknown({a, b, op}) |-> !$isunknown(result));

  // Combinational determinism: stable inputs -> stable output
  ap_stable: assert property ($stable({a, b, op}) |-> $stable(result));

  // Intent alarm: quotient is dropped in 8-bit result when non-zero
  ap_div_quotient_loss: assert property ((op == 2'b11 && b != 0 && (a / b) != 0) |-> 1'b0)
    else $error("calculator division drops non-zero quotient; result width likely needs >=16 bits");

  // Coverage: hit all ops and key corner cases
  cp_add:   cover property (op == 2'b00);
  cp_sub:   cover property (op == 2'b01);
  cp_mul:   cover property (op == 2'b10);
  cp_div0:  cover property (op == 2'b11 && b == 0);
  cp_divnz: cover property (op == 2'b11 && b != 0);

  // Overflow/borrow scenarios
  cp_add_carry: cover property ((op == 2'b00) && ((a + b) > 9'd255));
  cp_sub_borrow: cover property ((op == 2'b01) && (a < b));
  cp_mul_over: cover property ((op == 2'b10) && ((a * b) > 16'd255));

  // Division corner cases
  cp_div_q_nonzero: cover property ((op == 2'b11) && b != 0 && (a / b) != 0);
  cp_div_exact:     cover property ((op == 2'b11) && b != 0 && (a % b) == 0);
  cp_div_b_gt_a:    cover property ((op == 2'b11) && b != 0 && (a < b)); // remainder == a

endmodule