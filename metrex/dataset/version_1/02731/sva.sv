// SVA for freq_divider
module freq_divider_sva #(parameter width = 8) (
  input  logic              clk,
  input  logic              rst,
  input  logic [7:0]        div,
  input  logic [width-1:0]  out,
  input  logic [7:0]        count,
  input  logic              toggle
);

  default clocking cb @(posedge clk); endclocking

  // Asynchronous reset holds state low at sampled clock edges while rst=1
  a_reset_hold: assert property (@cb rst |-> (count==8'h00 && toggle==1'b0 && out=='0));

  // No X on key state when not in reset
  a_no_x:       assert property (@cb !rst |-> !$isunknown({count,toggle,out}));

  // Next-state: increment or wrap-to-0 on match; toggle only on match
  a_step_inc:   assert property (@cb disable iff (rst)
                        ($past(count) != $past(div)) |-> (count == $past(count)+8'h01 && toggle == $past(toggle)));
  a_step_match: assert property (@cb disable iff (rst)
                        ($past(count) == $past(div)) |-> (count == 8'h00 && toggle == ~$past(toggle)));

  // Toggle changes only when prior count==div
  a_toggle_only_on_match: assert property (@cb disable iff (rst)
                        $changed(toggle) |-> ($past(count) == $past(div)));

  // When prior count==0 and div==0, we toggle every cycle and stay at 0
  a_div0_behavior: assert property (@cb disable iff (rst)
                        ($past(div)==8'h00 && $past(count)==8'h00) |-> (count==8'h00 && toggle==~$past(toggle)));

  // out mirrors toggle on all bits
  a_out_mirrors_toggle: assert property (@cb disable iff (rst)
                        out == {width{toggle}});

  // Coverage
  c_toggle_rise:  cover property (@cb disable iff (rst) $rose(toggle));
  c_toggle_fall:  cover property (@cb disable iff (rst) $fell(toggle));
  c_match_event:  cover property (@cb disable iff (rst) ($past(count)==$past(div) && $changed(toggle)));
  c_wrap_no_toggle: cover property (@cb disable iff (rst)
                        ($past(count)==8'hFF && $past(div)!=8'hFF) ##1 (count==8'h00 && !$changed(toggle)));

endmodule

// Bind into DUT (accesses internal regs count/toggle)
bind freq_divider freq_divider_sva #(.width(width)) sva_i (
  .clk(clk),
  .rst(rst),
  .div(div),
  .out(out),
  .count(count),
  .toggle(toggle)
);