// SVA for calculator. Bind to the DUT.
module calculator_sva (calculator dut);

  default clocking cb @(posedge dut.start); endclocking

  // 8-bit expected result (truncation/wrap is inherent via return type)
  function automatic logic [7:0] exp(input logic [1:0] op, input logic [7:0] a, input logic [7:0] b);
    unique case (op)
      2'b00: exp = a + b;
      2'b01: exp = a - b;
      2'b10: exp = a * b;
      2'b11: exp = a / b; // only checked when b!=0
    endcase
  endfunction

  // Inputs must be known when operation starts
  a_inputs_known: assert property (! $isunknown({dut.op, dut.a, dut.b})))
    else $error("calculator: inputs X/Z at start");

  // No division by zero allowed
  a_no_div0: assert property (dut.op != 2'b11 || dut.b != 8'd0)
    else $error("calculator: divide by zero");

  // Correct arithmetic result appears in same cycle (after NBA) as start edge
  a_correct: assert property (
                (! $isunknown({dut.op,dut.a,dut.b})) && !(dut.op==2'b11 && dut.b==8'd0)
                |-> ##0 (dut.result == exp(dut.op,dut.a,dut.b))
              )
    else $error("calculator: wrong result");

  // Result must be known on valid operations
  a_result_known: assert property (
                     (! $isunknown({dut.op,dut.a,dut.b})) && !(dut.op==2'b11 && dut.b==8'd0)
                     |-> ##0 ! $isunknown(dut.result)
                   )
    else $error("calculator: result X/Z on valid op");

  // Functional coverage
  c_op_add:  cover property (dut.op==2'b00);
  c_op_sub:  cover property (dut.op==2'b01);
  c_op_mul:  cover property (dut.op==2'b10);
  c_op_div:  cover property (dut.op==2'b11 && dut.b!=8'd0);

  // Edge-case coverage
  c_add_overflow: cover property (dut.op==2'b00 && ({1'b0,dut.a}+{1'b0,dut.b})[8]);
  c_sub_underflow: cover property (dut.op==2'b01 && (dut.a < dut.b));
  c_mul_overflow: cover property (dut.op==2'b10 && (dut.a * dut.b) > 8'hFF);
  c_div_zero_attempt: cover property (dut.op==2'b11 && dut.b==8'd0);
  c_extremes_add: cover property (dut.op==2'b00 && dut.a==8'hFF && dut.b==8'h01);
  c_extremes_sub: cover property (dut.op==2'b01 && dut.a==8'h00 && dut.b==8'h01);
  c_extremes_mul: cover property (dut.op==2'b10 && dut.a==8'hFF && dut.b==8'h02);
  c_div_basic:    cover property (dut.op==2'b11 && dut.b==8'd1);

endmodule

bind calculator calculator_sva u_calculator_sva();