// SVA for the given design. Bind these modules to the DUT for checks and coverage.

// 4-bit free-running counter
module binary_counter_4bit_sva (input clk, input reset, input [3:0] q);
  default clocking cb @(posedge clk); endclocking

  // Reset holds zero; count increments every cycle when not in reset (wraps naturally)
  a_rst_hold: assert property (reset |-> q == 4'h0);
  a_inc:      assert property (disable iff (reset) q == $past(q) + 4'h1);

  // Known outputs
  a_q_known:  assert property (!$isunknown(q));

  // Coverage: see wrap 15->0
  c_wrap:     cover  property (disable iff (reset) $past(q) == 4'hF |=> q == 4'h0);
endmodule

bind binary_counter_4bit binary_counter_4bit_sva i_binary_counter_4bit_sva(.clk(clk), .reset(reset), .q(q));


// Loadable 4-bit counter with async reset and carry_out (saturates at F with carry_out=1)
module binary_counter_loadable_sva (
  input clk, input reset, input load, input [3:0] load_value,
  input [3:0] q, input carry_out
);
  default clocking cb @(posedge clk); endclocking

  // Reset behavior
  a_rst_hold:     assert property (reset |-> (q == 4'h5 && carry_out == 1'b0));

  // Load has priority; takes effect on the same clock
  a_load:         assert property (!reset && load |-> (q == load_value && carry_out == 1'b0));

  // Increment when not loading and not at max
  a_inc:          assert property (!reset && !load && (q != 4'hF) |-> (q == $past(q) + 4'h1 && carry_out == 1'b0));

  // Saturate at max with carry_out=1; q holds at F
  a_sat_cout:     assert property (!reset && !load && (q == 4'hF) |-> (q == $past(q) && carry_out == 1'b1));

  // No spurious carry_out
  a_cout_only_F:  assert property (!reset && carry_out |-> (q == 4'hF));

  // Known outputs
  a_known:        assert property (!$isunknown({q, carry_out}));

  // Coverage: exercise load, increment to F, assert carry_out, and load overriding F
  c_load:         cover  property (!reset && load);
  c_to_F:         cover  property (!reset && !load && (q == 4'hE) |-> q == 4'hF);
  c_cout:         cover  property (!reset && !load && (q == 4'hF) |-> carry_out);
  c_load_over_F:  cover  property (q == 4'hF ##1 load |-> (q == load_value && carry_out == 1'b0));
endmodule

bind binary_counter_loadable binary_counter_loadable_sva i_binary_counter_loadable_sva(
  .clk(clk), .reset(reset), .load(load), .load_value(load_value), .q(q), .carry_out(carry_out)
);


// Combinational control logic (assert using immediate assertions on any change)
module control_logic_sva (
  input select, input [3:0] q1, input [3:0] q2, input [3:0] q_out, input led, input carry_out
);
  // Functional equivalence of mux and LED drive
  always @* begin
    assert (q_out == (select ? q2 : q1)) else $error("q_out mismatch with select mux");
    assert (led == carry_out)            else $error("led must mirror carry_out");
  end

  // Coverage: both select directions toggled at least once
  c_sel_pos: cover property (@(posedge select) 1);
  c_sel_neg: cover property (@(negedge select) 1);
endmodule

bind control_logic control_logic_sva i_control_logic_sva(
  .select(select), .q1(q1), .q2(q2), .q_out(q_out), .led(led), .carry_out(carry_out)
);