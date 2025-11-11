// SystemVerilog Assertions for calculator
// Bind these to the DUT; focuses on correctness and concise full coverage.

module calculator_sva (
  input logic        clk,
  input logic        rst,
  input logic [1:0]  op,
  input logic [7:0]  in1,
  input logic [7:0]  in2,
  input logic [7:0]  result,
  input logic        overflow,
  input logic        zero
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Reset behavior (not disabled)
  a_reset_clears: assert property (@(posedge clk) rst |=> (result==8'h00 && !overflow && !zero));

  // Outputs known
  a_no_x_out:     assert property (!$isunknown({result,overflow,zero}));

  // Helpers (sampled from previous cycle operands)
  let add_sum   = $past(in1) + $past(in2);
  let add_res   = add_sum[7:0];
  let add_ovf   = (add_sum > 8'hFF);

  let sub_res   = ($past(in1) - $past(in2))[7:0];
  let sub_ovf   = ($past(in1) < $past(in2));

  let mul_prod  = $past(in1) * $past(in2);
  let mul_res   = mul_prod[7:0];
  let mul_ovf   = (mul_prod > 8'hFF);

  let div_by0   = ($past(in2) == 8'h00);
  let div_res   = div_by0 ? 8'h00 : ($past(in1) / $past(in2));
  let div_ovf   = 1'b0;
  let div_zero  = (div_res == 8'h00) || div_by0;

  // Functional correctness per op (next-cycle effect of current-cycle operands/op)
  a_add: assert property (op==2'b00 |=> (result==add_res && overflow==add_ovf && zero==(add_res==8'h00)));
  a_sub: assert property (op==2'b01 |=> (result==sub_res && overflow==sub_ovf && zero==(sub_res==8'h00)));
  a_mul: assert property (op==2'b10 |=> (result==mul_res && overflow==mul_ovf && zero==(mul_res==8'h00)));
  a_div: assert property (op==2'b11 |=> (result==div_res && overflow==div_ovf && zero==div_zero));

  // Zero flag should reflect result value each cycle
  a_zero_matches_result: assert property (zero == (result==8'h00));

  // Division must never overflow (explicit)
  a_div_never_ovf: assert property (op==2'b11 |=> overflow==1'b0);

  // Stimulus coverage (hit important scenarios)
  c_add_ovf_stim:        cover property (op==2'b00 && ((in1 + in2) > 8'hFF));
  c_add_zero_stim:       cover property (op==2'b00 && (((in1 + in2) & 8'hFF) == 8'h00));
  c_sub_underflow_stim:  cover property (op==2'b01 && (in1 < in2));
  c_sub_zero_stim:       cover property (op==2'b01 && (((in1 - in2) & 8'hFF) == 8'h00));
  c_mul_ovf_stim:        cover property (op==2'b10 && ((in1 * in2) > 8'hFF));
  c_mul_zero_stim:       cover property (op==2'b10 && (((in1 * in2) & 8'hFF) == 8'h00));
  c_div_by_zero_stim:    cover property (op==2'b11 && (in2==8'h00));
  c_div_zero_stim:       cover property (op==2'b11 && (in2!=8'h00) && (($unsigned(in1)/$unsigned(in2))==8'h00));

  // Observed flag coverage
  c_add_ovf_flag:        cover property (op==2'b00 |=> overflow);
  c_sub_ovf_flag:        cover property (op==2'b01 |=> overflow);
  c_mul_ovf_flag:        cover property (op==2'b10 |=> overflow);
  c_div_no_ovf_flag:     cover property (op==2'b11 |=> !overflow);
  c_zero_flag_seen:      cover property (1 |-> zero);

endmodule

bind calculator calculator_sva u_calculator_sva (.*);