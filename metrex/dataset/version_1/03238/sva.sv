// SVA for d_ff_set: synchronous load-enable DFF
module d_ff_set_sva #(parameter WIDTH=4)
(
  input clk,
  input [WIDTH-1:0] d,
  input set_b,
  input [WIDTH-1:0] q
);

  default clocking cb @(posedge clk); endclocking

  // Functional correctness
  a_load: assert property ( disable iff ($isunknown({set_b,d}))
                            set_b |-> (q == $past(d)) );

  a_hold: assert property ( disable iff ($isunknown(set_b))
                            !set_b |-> (q == $past(q)) );

  // Any change to q must be caused by an enabled clock edge
  a_change_requires_enable: assert property ( (q != $past(q)) |-> $past(set_b) );

  // Data changes must not affect q when disabled
  a_ignore_d_when_disabled: assert property ( !set_b && (d != $past(d)) |-> (q == $past(q)) );

  // No glitches between edges (q must be stable at negedge)
  a_no_glitch_negedge: assert property (@(negedge clk) $stable(q));

  // Coverage
  sequence s_load; set_b ##1 (q == $past(d)); endsequence
  c_load:  cover property (s_load);
  c_hold:  cover property (!set_b ##1 (q == $past(q)));
  c_back_to_back_loads: cover property (s_load ##1 s_load);
  c_q_change: cover property (q != $past(q));
  c_en_rise: cover property ($rose(set_b));
  c_en_fall: cover property ($fell(set_b));

endmodule

bind d_ff_set d_ff_set_sva #(.WIDTH(4)) dff_set_sva_i (.*);