// SVA for clock_gen: concise, high-quality checks + coverage
module clock_gen_sva (
  input logic        inclk0,
  input logic [1:0]  counter,
  input logic        c0,
  input logic        c1
);
  default clocking cb @(posedge inclk0); endclocking
  // Disable checks when counter is X/Z (e.g., power-up)
  default disable iff ($isunknown(counter));

  // Decode correctness
  a_c0_decode: assert property (c0 == (counter == 2'b00));
  a_c1_decode: assert property (c1 == (counter == 2'b01));
  a_onehot0:   assert property (!(c0 && c1));        // never both high
  a_idle_10:   assert property ((counter == 2'b10) |-> (!c0 && !c1));
  a_known_out: assert property (!$isunknown({c0,c1}));

  // Next-state behavior (including recovery from 2'b11)
  a_next_00: assert property ((counter == 2'b00) |=> (counter == 2'b01));
  a_next_01: assert property ((counter == 2'b01) |=> (counter == 2'b10));
  a_next_10: assert property ((counter == 2'b10) |=> (counter == 2'b00));
  a_from_11: assert property ((counter == 2'b11) |=> (counter == 2'b00));

  // Output pulse shape (single-cycle high, then low for 2 cycles)
  a_c0_pulse: assert property (c0 |-> !c0[*2]);
  a_c1_pulse: assert property (c1 |-> !c1[*2]);

  // Coverage: states, transitions, and output waveforms
  c_cycle:   cover property ((counter==2'b00) ##1 (counter==2'b01) ##1 (counter==2'b10) ##1 (counter==2'b00));
  c_c0_wave: cover property (c0 ##1 !c0[*2] ##1 c0);
  c_c1_wave: cover property (c1 ##1 !c1[*2] ##1 c1);
  c_recover: cover property ((counter==2'b11) ##1 (counter==2'b00));
endmodule

// Bind into DUT
bind clock_gen clock_gen_sva u_clock_gen_sva(
  .inclk0(inclk0),
  .counter(counter),
  .c0(c0),
  .c1(c1)
);