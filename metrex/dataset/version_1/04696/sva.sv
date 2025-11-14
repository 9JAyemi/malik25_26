// SVA for digital_clock
module digital_clock_sva (
  input        clk_in,
  input        rst,
  input        en,
  input  [2:0] counter,
  input        clk_out,
  input        clk_out_b
);

  default clocking cb @(posedge clk_in); endclocking
  default disable iff (rst);

  // Asynchronous reset takes effect immediately (after NBA)
  a_async_reset_now: assert property (@(posedge rst) ##0
                                      (counter==3'b000 && clk_out==1'b0 && clk_out_b==1'b0));
  // Hold reset values while rst=1 on clock edges
  a_hold_during_rst: assert property (@(posedge clk_in)
                                      rst |-> (counter==3'b000 && clk_out==1'b0 && clk_out_b==1'b0));

  // No X/Z after reset deasserted
  a_known: assert property (!$isunknown({counter, clk_out, clk_out_b}));

  // Counter behavior
  a_cnt_inc_when_en:  assert property (en  |-> counter == $past(counter) + 3'b001);
  a_cnt_hold_when_dis: assert property (!en |-> counter == $past(counter));

  // Output toggles happen exactly at intended counts (based on old counter)
  a_out_tog_on_3:   assert property ((en && $past(counter)==3'b011) |-> (clk_out   == ~$past(clk_out)));
  a_outb_tog_on_2:  assert property ((en && $past(counter)==3'b010) |-> (clk_out_b == ~$past(clk_out_b)));

  // Outputs change only when their conditions are met
  a_out_only_when_3:  assert property ($changed(clk_out)   |-> (en && $past(counter)==3'b011));
  a_outb_only_when_2: assert property ($changed(clk_out_b) |-> (en && $past(counter)==3'b010));

  // When disabled, everything holds
  a_hold_when_dis: assert property (!en |-> ($stable(counter) && $stable(clk_out) && $stable(clk_out_b)));

  // Never toggle both outputs in the same cycle
  a_no_simul_toggle: assert property (!($changed(clk_out) && $changed(clk_out_b)));

  // Coverage
  c_outb_toggle:    cover property (en && $past(counter)==3'b010 && clk_out_b == ~$past(clk_out_b));
  c_out_toggle:     cover property (en && $past(counter)==3'b011 && clk_out   == ~$past(clk_out));
  c_wraparound:     cover property (en && $past(counter)==3'b111 && counter==3'b000);
  c_outb_then_out:  cover property ((en && $past(counter)==3'b010) ##1 (en && $past(counter)==3'b011));
  c_en_pulse:       cover property (!en ##1 en);

endmodule

bind digital_clock digital_clock_sva u_digital_clock_sva (
  .clk_in(clk_in),
  .rst(rst),
  .en(en),
  .counter(counter),
  .clk_out(clk_out),
  .clk_out_b(clk_out_b)
);