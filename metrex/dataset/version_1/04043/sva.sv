// SVA for shift_register and its d_flip_flop instances
module shift_register_sva (input logic clk, serial_in, serial_out, q0, q1, q2);
  default clocking cb @(posedge clk); endclocking

  logic [2:0] cnt; initial cnt = '0;
  always @(posedge clk) cnt <= (cnt == 3'd7) ? cnt : cnt + 1;
  wire past1_ok = (cnt >= 1);
  wire past3_ok = (cnt >= 3);

  // Structural tie-off
  a_out_tied: assert property (serial_out == q2);

  // Stage-by-stage shift (guard unknowns and first-cycle)
  a_s0: assert property (past1_ok && !$isunknown($past(serial_in))) |-> (q0 == $past(serial_in));
  a_s1: assert property (past1_ok && !$isunknown($past(q0)))       |-> (q1 == $past(q0));
  a_s2: assert property (past1_ok && !$isunknown($past(q1)))       |-> (q2 == $past(q1));

  // End-to-end latency = 3 cycles
  a_latency3: assert property (past3_ok && !$isunknown($past(serial_in,3))) |-> (serial_out == $past(serial_in,3));

  // No glitches between clocks
  a_no_glitch_qs: assert property (@(negedge clk) $stable({q0,q1,q2,serial_out}));

  // Coverage: both edges propagate and a pulse walks the pipeline
  c_rise_propagates: cover property ($rose(serial_in) ##3 $rose(serial_out));
  c_fall_propagates: cover property ($fell(serial_in) ##3 $fell(serial_out));
  c_one_pulse_walks: cover property (serial_in ##1 q0 ##1 q1 ##1 q2 ##1 serial_out);
endmodule

module dff_sva (input logic clk, d, q);
  default clocking cb @(posedge clk); endclocking
  bit seen; initial seen = 0;
  always @(posedge clk) seen <= 1;

  a_q_follows_d: assert property (seen && !$isunknown($past(d))) |-> (q == $past(d));
  a_q_stable_between: assert property (@(negedge clk) $stable(q));
endmodule

bind shift_register shift_register_sva shift_register_sva_i
  (.clk(clk), .serial_in(serial_in), .serial_out(serial_out), .q0(q0), .q1(q1), .q2(q2));

bind d_flip_flop dff_sva dff_sva_i (.clk(clk), .d(d), .q(q));