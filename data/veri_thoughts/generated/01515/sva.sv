module register_32bit_parallel_load_sva (
  input logic CLK,
  input logic AR,
  input logic E,
  input logic [31:0] O,
  input logic [31:0] Q,
  input logic Overflow_flag_A
);

  // During reset, Q and Overflow_flag_A must be 0.
  reset_outputs_low: assert property (
    @(posedge CLK) !AR |-> (Q == 32'd0) && (Overflow_flag_A == 1'b0)
  );

  // When E is HIGH, Q loads O on the next cycle.
  load_q_on_E: assert property (
    @(posedge CLK) disable iff (!AR) E |=> (Q == $past(O))
  );

  // When E is HIGH, Overflow_flag_A clears on the next cycle.
  clear_flag_on_E: assert property (
    @(posedge CLK) disable iff (!AR) E |=> (Overflow_flag_A == 1'b0)
  );

  // When E is LOW, Q holds its previous value on the next cycle.
  hold_q_when_E_low: assert property (
    @(posedge CLK) disable iff (!AR) !E |=> (Q == $past(Q))
  );

  // When E is LOW, Overflow_flag_A reflects whether prior Q was all 1s.
  update_flag_when_E_low: assert property (
    @(posedge CLK) disable iff (!AR) !E |=> (Overflow_flag_A == ($past(Q) == 32'hFFFF_FFFF))
  );

  // With consecutive hold cycles, Overflow_flag_A remains stable.
  flag_stable_across_holds: assert property (
    @(posedge CLK) disable iff (!AR) $past(AR) && !$past(E) && !E |-> (Overflow_flag_A == $past(Overflow_flag_A))
  );

endmodule