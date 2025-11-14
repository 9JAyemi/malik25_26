// Bindable SVA checker for ring_delay
bind ring_delay ring_delay_sva u_ring_delay_sva (
  .clk(clk),
  .d(d),
  .delay(delay),
  .q(q),
  .shift_reg(shift_reg),
  .delay_counter(delay_counter)
);

module ring_delay_sva(
  input  logic        clk,
  input  logic        d,
  input  logic [3:0]  delay,
  input  logic        q,
  input  logic [2:0]  shift_reg,
  input  logic [3:0]  delay_counter
);
  default clocking cb @(posedge clk); endclocking
  default disable iff ($isunknown({clk,d,delay,q,shift_reg,delay_counter}));

  // Shift register correctness
  assert property (1'b1 |=> shift_reg == {$past(shift_reg[1:0]), $past(d)});
  assert property (1'b1 |-> ##3 (shift_reg[2] == $past(d,3)));

  // Counter: equal branch (update q from pre-shift bit and reset counter)
  assert property ( (delay_counter == delay)
                    |=> (delay_counter == 4'd0 && q == $past(shift_reg[2])) );

  // Counter: non-equal branch (increment by 1 mod 16, hold q)
  assert property ( (delay_counter != delay)
                    |=> (delay_counter == ($past(delay_counter) + 4'd1) && q == $past(q)) );

  // q must only change on cycles the equal-branch was taken
  assert property ( $changed(q) |-> $past(delay_counter == delay) );

  // End-to-end: on an update, q reflects d from 4 cycles earlier
  assert property ( (delay_counter == delay) |=> (q == $past(d,4)) );

  // Liveness: if delay holds constant for 16 cycles, equality must occur within 16 cycles
  assert property ( $stable(delay) [*16] |-> ##[0:15] (delay_counter == delay) );

  // Coverage
  cover property ( (delay_counter == delay) ##1 (delay_counter == 4'd0 && q == $past(shift_reg[2])) );
  cover property ( (delay_counter == 4'hF && delay != 4'hF) ##1 (delay_counter == 4'h0) ); // wrap increment
  cover property ( $changed(q) );
  cover property ( (delay == 4'd0  && delay_counter == 4'd0) ##1 (delay_counter == 4'd0) ); // min delay case
  cover property ( (delay == 4'd15 && delay_counter == 4'd15) ##1 (delay_counter == 4'd0) ); // max delay case
  cover property ( $changed(d) ##3 $changed(shift_reg[2]) ); // observe 3-cycle shift through SR
endmodule