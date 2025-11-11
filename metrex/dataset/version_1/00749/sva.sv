// SVA for ripple_carry_adder (concise, high-quality). Note: This DUT’s carry computation is functionally wrong; assertions below will expose it.

`ifndef RCA_SVA
`define RCA_SVA

// Checker module (bound into DUT)
module rca_sva (
  input  logic [3:0] in0,
  input  logic [3:0] in1,
  input  logic       carry_in,
  input  logic [3:0] sum,
  input  logic       carry_out,
  input  logic [3:0] temp_sum,
  input  logic       temp_carry
);

  // Trigger on input changes for functional checks; outputs for spurious-change checks
  default clocking cb_in @(in0 or in1 or carry_in); endclocking
  clocking cb_out @(sum or carry_out); endclocking

  // Functional correctness: full 5-bit result must match
  property p_full_add;
    disable iff ($isunknown({in0,in1,carry_in}))
      1 |-> ##0 ({carry_out,sum} == in0 + in1 + carry_in);
  endproperty
  assert property (p_full_add);

  // Outputs known when inputs known
  property p_known_out_when_known_in;
    disable iff ($isunknown({in0,in1,carry_in}))
      1 |-> ##0 ! $isunknown({sum,carry_out});
  endproperty
  assert property (p_known_out_when_known_in);

  // Outputs don't change unless inputs change
  property p_no_spurious_out_change;
    $changed({sum,carry_out}) |-> $changed({in0,in1,carry_in});
  endproperty
  assert property (@cb_out p_no_spurious_out_change);

  // Internal consistency with coding intent
  property p_sum_eq_temp_sum; 1 |-> ##0 (sum == temp_sum); endproperty
  assert property (p_sum_eq_temp_sum);

  property p_temp_sum_math;
    disable iff ($isunknown({in0,in1,carry_in}))
      1 |-> ##0 (temp_sum == (in0 + in1 + carry_in)[3:0]);
  endproperty
  assert property (p_temp_sum_math);

  property p_cout_eq_temp_carry; 1 |-> ##0 (carry_out == temp_carry); endproperty
  assert property (p_cout_eq_temp_carry);

  // Intended carry math (will fail with current DUT)
  property p_temp_carry_math;
    disable iff ($isunknown({in0,in1,carry_in}))
      1 |-> ##0 (temp_carry == ((in0 + in1 + carry_in) > 4'hF));
  endproperty
  assert property (p_temp_carry_math);

  // Compact, meaningful coverage
  cover property (@cb_in ! $isunknown({in0,in1,carry_in}) ##0 (in0==4'h0 && in1==4'h0 && !carry_in && sum==4'h0 && !carry_out)); // 0+0+0
  cover property (@cb_in ! $isunknown({in0,in1,carry_in}) ##0 ((in0 + in1 + carry_in) == 5'd15 && sum==4'hF && !carry_out));     // boundary: 15
  cover property (@cb_in ! $isunknown({in0,in1,carry_in}) ##0 ((in0 + in1 + carry_in) == 5'd16 && sum==4'h0 &&  carry_out));     // boundary: 16
  cover property (@cb_in ! $isunknown({in0,in1,carry_in}) ##0 ((in0 + in1 + carry_in) >  5'd15 && carry_out));                    // overflow seen
  cover property (@cb_in ! $isunknown({in0,in1,carry_in}) ##0 ((in0 + in1 + carry_in) <= 5'd15 && !carry_out));                   // no overflow
  cover property (@cb_in ! $isunknown({in0,in1,carry_in}) ##0 (carry_in && in0==0 && in1==0 && sum==1 && !carry_out));            // carry-in passthrough
endmodule

// Bind into DUT (access internals for stronger checks)
bind ripple_carry_adder rca_sva u_rca_sva (
  .in0(in0),
  .in1(in1),
  .carry_in(carry_in),
  .sum(sum),
  .carry_out(carry_out),
  .temp_sum(temp_sum),
  .temp_carry(temp_carry)
);

`endif