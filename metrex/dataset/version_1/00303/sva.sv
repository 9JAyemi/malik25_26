// SVA for chatgpt_generate_edge_detect
// Bind into the DUT or place inside the module under `ifdef SVA
module chatgpt_generate_edge_detect_sva (
  input  logic clk,
  input  logic rst_n,
  input  logic A,
  input  logic rise,
  input  logic down,
  input  logic prev_A
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Asynchronous reset drives all regs low
  a_reset_vals: assert property (@(negedge rst_n) (rise==0 && down==0 && prev_A==0));

  // prev_A tracks A from the previous cycle (after coming out of reset)
  a_prevA_tracks: assert property ($past(rst_n) |-> prev_A == $past(A));

  // Direction-correct, one-cycle pulses mapped to prior-cycle A edges
  a_rise_on_r_edge:  assert property ($past(rst_n) |-> rise == ( $past(A) && !$past(A,2)));
  a_down_on_f_edge:  assert property ($past(rst_n) |-> down == (! $past(A) &&  $past(A,2)));

  // No pulse when no edge last cycle; and pulses are mutually exclusive
  a_no_pulse_when_stable: assert property ($past(rst_n) && ($past(A) === $past(A,2)) |-> !(rise || down));
  a_onehot0:              assert property (!(rise && down));

  // Pulses are single-cycle (never asserted in consecutive cycles)
  a_rise_one_cycle: assert property (rise |-> ##1 !rise);
  a_down_one_cycle: assert property (down |-> ##1 !down);

  // Optional: no X/Z on outputs when out of reset
  a_no_x: assert property (!$isunknown({rise,down,prev_A}));

  // Coverage
  c_rise:         cover property (rise);
  c_down:         cover property (down);
  c_rise_then_down: cover property (rise ##1 down);
  c_down_then_rise: cover property (down ##1 rise);
  c_quiet_3:      cover property ((!rise && !down)[*3]);
endmodule

// Example bind (connects to internal prev_A by name within the bound scope)
bind chatgpt_generate_edge_detect chatgpt_generate_edge_detect_sva sva (
  .clk(clk),
  .rst_n(rst_n),
  .A(A),
  .rise(rise),
  .down(down),
  .prev_A(prev_A)
);