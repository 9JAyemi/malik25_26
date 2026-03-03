// SVA for rotator. Binds to any instance of module rotator.
module rotator_sva #(parameter int W = 100)
(
  input logic              clk,
  input logic              load,
  input logic [1:0]        ena,
  input logic [W-1:0]      data,
  input logic [W-1:0]      q
);
  default clocking cb @(posedge clk); endclocking

  // past-valid guard
  logic past_v;
  initial past_v = 1'b0;
  always_ff @(posedge clk) past_v <= 1'b1;

  // Load dominates all enables
  a_load_dominates: assert property (past_v && load |-> q == data);

  // Hold when idle (no load, no enable)
  a_idle_hold:      assert property (past_v && !load && (ena == 2'b00) |-> q == $past(q));

  // Rotate right by 1 when ena[0]==1 (priority over ena[1])
  a_rot_r1:         assert property (past_v && !load && ena[0]
                                     |-> q == { $past(q)[0], $past(q)[W-1:1] });

  // Rotate left by 1 only when ena[1]==1 and ena[0]==0
  a_rot_l1:         assert property (past_v && !load && !ena[0] && ena[1]
                                     |-> q == { $past(q)[W-2:0], $past(q)[W-1] });

  // When both bits are 1, priority implies right-rotate-by-1 (exposes unreachable 2-bit branch)
  a_both_bits_prio: assert property (past_v && !load && (ena == 2'b11)
                                     |-> q == { $past(q)[0], $past(q)[W-1:1] });

  // Output changes only when commanded (load or some enable was set)
  a_change_has_cause: assert property (past_v && !$isunknown($past(q)) && (q != $past(q))
                                       |-> $past(load || (ena != 2'b00)));

  // Rotations preserve popcount
  a_popcount_preserved: assert property (past_v && !load && (ena != 2'b00)
                                         |-> $countones(q) == $countones($past(q)));

  // Functional coverage
  c_load:  cover property (past_v && load);
  c_idle:  cover property (past_v && !load && (ena == 2'b00));
  c_r1:    cover property (past_v && !load && (ena[0] == 1'b1));
  c_l1:    cover property (past_v && !load && (ena == 2'b10));
  c_both:  cover property (past_v && !load && (ena == 2'b11));
endmodule

bind rotator rotator_sva #(.W(100)) rotator_sva_bind (.*);