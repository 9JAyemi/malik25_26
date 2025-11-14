// SVA for counter. Bind this to the DUT.
module counter_sva #(parameter WIDTH=8) (
  input clk,
  input rst,
  input enable,
  input [WIDTH-1:0] mod,
  input [WIDTH-1:0] count,
  input done
);
  default clocking cb @(posedge clk); endclocking
  default disable iff ($initstate);

  // Reset behavior
  ap_reset_vals: assert property (rst |-> (count=={WIDTH{1'b0}} && done==1'b0));

  // Hold when not enabled (and not in reset previous cycle)
  ap_hold_idle: assert property ($past(!rst && !enable) |-> (count==$past(count) && done==$past(done)));

  // Increment on enabled, non-wrap path (decision uses previous count and current mod)
  ap_inc: assert property ($past(!rst && enable) && ($past(count) != (mod-1))
                           |-> (count == $past(count)+1 && done==1'b0));

  // Wrap on enabled, wrap path
  ap_wrap: assert property ($past(!rst && enable) && ($past(count) == (mod-1))
                            |-> (count == {WIDTH{1'b0}} && done==1'b1));

  // Under enable, done reflects wrap decision exactly
  ap_done_eq_wrap_when_en: assert property ($past(!rst && enable)
                                           |-> (done == ($past(count) == (mod-1))));

  // Outputs should not be X/Z after reset deasserts
  ap_no_x: assert property (!rst |-> !$isunknown({count,done}));

  // Optional: configuration sanity (disallow mod==0 if undesired)
  // ap_mod_nonzero: assert property (!rst |-> (mod != '0));

  // Coverage
  cp_reset_deassert: cover property (rst ##1 !rst);
  cp_increment:      cover property ($past(!rst && enable) && ($past(count)!=(mod-1))
                                     && (count==$past(count)+1) && (done==0));
  cp_wrap:           cover property ($past(!rst && enable) && ($past(count)==(mod-1))
                                     && (count==0) && (done==1));
  // Mod change causing immediate wrap
  cp_mod_change_wrap: cover property ($past(!rst && enable) && (mod!=$past(mod)) && ($past(count)==(mod-1))
                                      && (count==0) && (done==1));
  // mod==1 behavior under enable
  cp_mod1:           cover property (!rst && enable && (mod=={{(WIDTH-1){1'b0}},1'b1}) && (count==0) && (done==1));
endmodule

bind counter counter_sva #(.WIDTH(WIDTH)) counter_sva_b (.*);