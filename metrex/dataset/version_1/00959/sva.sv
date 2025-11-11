// SVA for counter_2bit
// Bind-in checker; references internal regs via port matching
module counter_2bit_sva (
  input  logic       CLK,
  input  logic       RESET,
  input  logic       Q1,
  input  logic       Q0,
  input  logic [1:0] count_reg,
  input  logic [1:0] next_count_reg
);

  default clocking cb @(posedge CLK); endclocking

  // No X/Z on key signals at clock edges
  assert property (cb !$isunknown({Q1,Q0,count_reg,next_count_reg}));

  // Outputs mirror state (sampled on CLK and after async RESET edge)
  assert property (@(posedge CLK or posedge RESET) ##0 {Q1,Q0} == count_reg);

  // Async RESET forces state to 00 immediately and holds while asserted
  assert property (@(posedge RESET) ##0 (count_reg == 2'b00));
  assert property (cb RESET |-> (count_reg == 2'b00));

  // On first clock after RESET deassertion, go to 01
  assert property (cb $past(RESET) && !RESET |-> (count_reg == 2'b01));

  // Sequential behavior: increment by 1 mod-4 each cycle when not in RESET
  assert property (cb disable iff (RESET) count_reg == $past(count_reg) + 2'd1);

  // Registered update comes from next_count_reg
  assert property (cb disable iff (RESET) count_reg == $past(next_count_reg));

  // Combinational next state matches +1 mod-4
  assert property (@(posedge CLK) next_count_reg == (count_reg + 2'd1));

  // Coverage: observe full 4-state cycle and bit activity
  cover property (cb disable iff (RESET)
    (count_reg==2'b00) ##1 (count_reg==2'b01) ##1 (count_reg==2'b10) ##1 (count_reg==2'b11) ##1 (count_reg==2'b00)
  );
  cover property (cb disable iff (RESET) Q0 != $past(Q0));
  cover property (cb disable iff (RESET) $changed(Q1));

endmodule

bind counter_2bit counter_2bit_sva sva (.*);