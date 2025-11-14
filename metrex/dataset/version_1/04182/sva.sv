// SVA for led_sreg_driver
// Bind into DUT; assertions reference DUT internals
module led_sreg_driver_sva #(parameter int COUNT=8, INVERT=0, PRESCALE=31) ();

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  function automatic logic inv(input logic v);
    return INVERT ? ~v : v;
  endfunction

  // Basic ranges
  assert property (prescale_count_reg <= PRESCALE);
  assert property (count_reg <= COUNT);

  // Enable pulse periodicity and alignment with prescaler
  sequence en; enable_reg; endsequence
  assert property (en |-> !enable_reg[*PRESCALE] ##1 enable_reg);
  assert property (enable_reg |-> $past(prescale_count_reg)==0 && prescale_count_reg==PRESCALE);

  // sreg_clk phase on enable events
  assert property (enable_reg &&  cycle_reg |-> sreg_clk==1);
  assert property (enable_reg && !cycle_reg |-> sreg_clk==0);

  // Outputs change only on enable events
  assert property ($changed(sreg_clk) |-> $past(enable_reg));
  assert property ($changed(sreg_ld)  |-> $past(enable_reg));
  assert property ($changed(sreg_d)   |-> $past(enable_reg));

  // sreg_ld only at end-of-frame; never with sreg_clk
  assert property (enable_reg && (count_reg==COUNT) && !cycle_reg |-> sreg_ld==1);
  assert property (enable_reg && !((count_reg==COUNT) && !cycle_reg) |-> sreg_ld==0);
  assert property (!(sreg_ld && sreg_clk));

  // sreg_d inversion mapping
  generate
    if (INVERT==0) begin
      assert property (sreg_d == sreg_d_reg);
    end else begin
      assert property (sreg_d == ~sreg_d_reg);
    end
  endgenerate

  // sreg_d correctness per index (sampled on low phase enables)
  assert property (enable_reg && !cycle_reg && (count_reg>0) && (count_reg<COUNT)
                   |-> sreg_d == inv(led_reg[count_reg]));
  assert property (enable_reg && !cycle_reg && (count_reg==0) && update_reg
                   |-> sreg_d == inv(led_reg[0]));
  assert property (enable_reg && !cycle_reg && (count_reg==COUNT)
                   |-> sreg_d == inv(1'b0));

  // Data stable on clock-high enable
  assert property (enable_reg && cycle_reg |-> $stable(sreg_d));

  // Count progression on enable events
  assert property (enable_reg && !cycle_reg && (count_reg>0) && (count_reg<COUNT)
                   |=> count_reg == $past(count_reg)+1);
  assert property (enable_reg && !cycle_reg && (count_reg==COUNT)
                   |=> count_reg == 0);
  assert property (enable_reg &&  cycle_reg
                   |=> count_reg == $past(count_reg));

  // Update tracking
  assert property ((led_reg != $past(led_reg)) |-> update_reg);
  assert property (enable_reg && !cycle_reg && (count_reg==0) && update_reg
                   |=> update_reg==0);

  // Synchronizer behavior
  assert property (led_sync_reg_2 == $past(led_sync_reg_1));
  assert property (led_sync_reg_1 == $past(led));

  // Reset drives known state next cycle (override default disable)
  assert property (disable iff (1'b0)
                   rst |=> (count_reg==0 && prescale_count_reg==0 && enable_reg==1'b0 &&
                            update_reg==1'b1 && cycle_reg==1'b0 && led_reg=={COUNT{1'b0}} &&
                            sreg_d_reg==1'b0 && sreg_ld_reg==1'b0 && sreg_clk_reg==1'b0));

  // Coverage: full frame shift and latch
  cover property (enable_reg && !cycle_reg && (count_reg==0) && update_reg
                  ##1 (enable_reg && cycle_reg)[*COUNT]
                  ##1 (enable_reg && !cycle_reg && (count_reg==COUNT))
                  ##1 (enable_reg && !cycle_reg && (count_reg==0)));

  // Coverage: update observed then consumed
  cover property ((led_reg != $past(led_reg))
                  ##[1:$] (enable_reg && !cycle_reg && (count_reg==0) && update_reg));

  // Coverage: prescaler spacing
  cover property (enable_reg ##1 !enable_reg[*PRESCALE] ##1 enable_reg);

endmodule

bind led_sreg_driver led_sreg_driver_sva #(.COUNT(COUNT), .INVERT(INVERT), .PRESCALE(PRESCALE)) led_sreg_driver_sva_i ();