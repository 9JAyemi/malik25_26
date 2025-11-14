// SVA for simple_calculator
// Bind this module to the DUT instance.

module simple_calculator_sva (
  input clk,
  input reset,
  input  signed [7:0]  A,
  input  signed [7:0]  B,
  input         [1:0]  op,
  input  signed [15:0] result,
  input                valid
);

  // Golden model with Verilog width semantics
  function automatic signed [15:0] exp_res(input signed [7:0] a, b, input [1:0] o);
    automatic signed [7:0]  t8;
    automatic signed [15:0] t16;
    begin
      unique case (o)
        2'b00: begin t8 = a + b; exp_res = {{8{t8[7]}}, t8}; end      // 8b wrap, sign-extend
        2'b01: begin t8 = a - b; exp_res = {{8{t8[7]}}, t8}; end      // 8b wrap, sign-extend
        2'b10: begin t16 = a * b; exp_res = t16; end                  // 16b product
        2'b11: begin
          if (b == 0) exp_res = 'x;                                  // div-by-0 -> X
          else begin t8 = a / b; exp_res = {{8{t8[7]}}, t8}; end      // 8b quotient, sign-extend
        end
        default: exp_res = 16'sd0;
      endcase
    end
  endfunction

  // Basic sanity/X checks
  a_no_x_inputs: assert property (@(posedge clk) !$isunknown({reset,op,A,B}));
  a_no_x_outputs_when_valid: assert property (@(posedge clk) valid |-> (!$isunknown(result) && !$isunknown(valid)));

  // Reset and valid behavior
  a_valid_eq_reset: assert property (@(posedge clk) valid == !reset);
  a_reset_drives_zero: assert property (@(posedge clk) reset |-> (result == 16'sd0 && valid == 1'b0));

  // Functional correctness (1-cycle registered)
  a_result_matches_model: assert property (@(posedge clk)
    disable iff (reset)
    result == exp_res($past(A,1,reset), $past(B,1,reset), $past(op,1,reset))
  );

  // Division by zero must not be issued
  a_no_div_by_zero: assert property (@(posedge clk) (!reset && op==2'b11) |-> (B != 0));

  // Coverage: ops exercised and key corner cases
  c_add:  cover property (@(posedge clk) !reset && op==2'b00);
  c_sub:  cover property (@(posedge clk) !reset && op==2'b01);
  c_mul:  cover property (@(posedge clk) !reset && op==2'b10);
  c_div:  cover property (@(posedge clk) !reset && op==2'b11 && B!=0);

  // Signed overflow scenarios for 8-bit add/sub (pre-register)
  c_add_overflow: cover property (@(posedge clk)
    !reset && op==2'b00 && (A[7]==B[7]) && ((A+B)[7] != A[7])
  );
  c_sub_overflow: cover property (@(posedge clk)
    !reset && op==2'b01 && (A[7]!=B[7]) && ((A-B)[7] != A[7])
  );

  // Signed divide with opposite signs
  c_div_mixed_signs: cover property (@(posedge clk)
    !reset && op==2'b11 && B!=0 && (A[7]^B[7])
  );

  // Reset activity covered
  c_reset_seen: cover property (@(posedge clk) reset);

endmodule

bind simple_calculator simple_calculator_sva u_simple_calculator_sva (
  .clk(clk),
  .reset(reset),
  .A(A),
  .B(B),
  .op(op),
  .result(result),
  .valid(valid)
);