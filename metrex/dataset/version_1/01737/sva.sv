// Bindable SVA for multiplier. Bind into your DUT instance.
bind multiplier multiplier_sva sva();

module multiplier_sva ();
  // Bound inside multiplier; can reference internal regs
  default clocking cb @(posedge clk); endclocking
  default disable iff ($initstate);

  // No X/Zs on key state
  a_no_x: assert property ( !$isunknown({counter, multiplier, multiplicand, P}) );

  // Initialization when counter==0
  a_init: assert property ( $past(counter)==6'd0 |-> (counter==6'd11 && P==24'd0 && multiplier==Q && multiplicand==Q_reg) );

  // Counter strictly decrements while active
  a_cnt_step: assert property ( $past(counter)>6'd0 |-> counter == $past(counter) - 6'd1 );

  // Shifts occur each active cycle
  a_shifts: assert property ( $past(counter)>6'd0 |-> (multiplier == ($past(multiplier) >> 1) &&
                                                       multiplicand == ($past(multiplicand) << 1)) );

  // Accumulate only when LSB is 1; hold otherwise
  a_add_when_1: assert property ( $past(counter)>6'd0 && $past(multiplier[0]) |-> P == $past(P) + { $past(multiplicand), 10'b0 } );
  a_hold_when_0: assert property ( $past(counter)>6'd0 && !$past(multiplier[0]) |-> P == $past(P) );

  // Final cycle produces product of captured operands (11 cycles after init)
  a_final_result: assert property ( $past(counter)==6'd1 |-> P == $past(Q,11) * $past(Q_reg,11) );

  // Multiplier should be fully shifted out at end
  a_final_mult_zero: assert property ( $past(counter)==6'd1 |-> multiplier == 11'd0 );

  // Coverage
  c_full_run:        cover property ( counter==6'd0 ##11 (P == $past(Q,11) * $past(Q_reg,11)) );
  c_add_exercised:   cover property ( $past(counter)>6'd0 && $past(multiplier[0]) );
  c_skip_exercised:  cover property ( $past(counter)>6'd0 && !$past(multiplier[0]) );
  c_zero_operand:    cover property ( (counter==6'd0 && (Q==11'd0 || Q_reg==11'd0)) ##11 (P==24'd0) );
  c_max_operands:    cover property ( (counter==6'd0 && Q==11'h7FF && Q_reg==11'h7FF) ##11 (P == $past(Q,11) * $past(Q_reg,11)) );
endmodule