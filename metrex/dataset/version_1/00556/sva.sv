// SVA for RotaryInterface
module RotaryInterface_sva (
  input logic        clock,
  input logic        reset,
  input logic [1:0]  rotary,

  // internal regs
  input logic        s_Filter1,
  input logic        s_Filter2,
  input logic        s_Filter1Delay,
  input logic        s_DoneRotaryLeft,
  input logic        s_DoneRotaryRight,

  // outputs
  input logic        rotary_left,
  input logic        rotary_right
);
  default clocking cb @(posedge clock); endclocking
  default disable iff (reset);

  // Knownness
  assert property (!$isunknown({reset,rotary}));
  assert property (##0 !$isunknown({rotary_left,rotary_right}));

  // Reset drives all state/output low (after NBA in same cycle)
  assert property (reset |-> ##0
                   (s_Filter1==0 && s_Filter2==0 &&
                    s_Filter1Delay==0 &&
                    s_DoneRotaryLeft==0 && s_DoneRotaryRight==0 &&
                    !rotary_left && !rotary_right));

  // Filter update mapping
  assert property ((rotary==2'b00) |=> (s_Filter1==0 && $stable(s_Filter2)));
  assert property ((rotary==2'b11) |=> (s_Filter1==1 && $stable(s_Filter2)));
  assert property ((rotary==2'b01) |=> ($stable(s_Filter1) && s_Filter2==0));
  assert property ((rotary==2'b10) |=> ($stable(s_Filter1) && s_Filter2==1));

  // s_Filter1Delay is a 1-cycle delay of s_Filter1
  assert property (s_Filter1Delay == $past(s_Filter1));

  // Event detect on rising of s_Filter1 (as coded): s_Filter1 && !s_Filter1Delay
  sequence rise_evt; s_Filter1 && !s_Filter1Delay; endsequence

  // On event: 1-cycle pulse left/right based on s_Filter2; done flags mirror pulse; next cycle all clear
  assert property (rise_evt |-> ##0
                   (rotary_left == !s_Filter2 && rotary_right == s_Filter2 &&
                    s_DoneRotaryLeft == !s_Filter2 && s_DoneRotaryRight == s_Filter2)
                   ##1 (!rotary_left && !rotary_right &&
                        !s_DoneRotaryLeft && !s_DoneRotaryRight));

  // No spurious pulses or done flags without event
  assert property ((!rise_evt) |-> ##0 (!rotary_left && !rotary_right &&
                                        !s_DoneRotaryLeft && !s_DoneRotaryRight));

  // Mutual exclusivity
  assert property (##0 !(rotary_left && rotary_right));

  // Covers
  cover property (rise_evt &&  s_Filter2); // right pulse
  cover property (rise_evt && !s_Filter2); // left pulse
endmodule

// Bind into DUT
bind RotaryInterface RotaryInterface_sva sva_i (
  .clock(clock),
  .reset(reset),
  .rotary(rotary),
  .s_Filter1(s_Filter1),
  .s_Filter2(s_Filter2),
  .s_Filter1Delay(s_Filter1Delay),
  .s_DoneRotaryLeft(s_DoneRotaryLeft),
  .s_DoneRotaryRight(s_DoneRotaryRight),
  .rotary_left(rotary_left),
  .rotary_right(rotary_right)
);