// SVA for ADCinterface
module ADCinterface_sva
(
  input logic        clk,
  input logic        reset_n,
  input logic        CS_n,
  input logic        RD_n,
  input logic        WR_n,
  input logic [7:0]  count
);

  default clocking cb @(posedge clk); endclocking
  // Assertions that must hold even in reset
  a_cs_rd_const: assert property (@cb (CS_n==1'b0 && RD_n==1'b0));
  a_no_x:        assert property (@cb !$isunknown({CS_n,RD_n,WR_n,count}));

  // While reset low, hold cleared
  a_hold_in_reset: assert property (@cb !reset_n |-> (count==8'd0 && WR_n==1'b0));

  // On reset deassert, start correctly on next clk
  a_post_reset_start: assert property (@cb $rose(reset_n) |=> (count==8'd1 && WR_n==1'b0));

  // Count stays in legal range
  default disable iff (!reset_n)
  a_count_range:      assert property (@cb count <= 8'd200);

  // Count next-state: increment unless 200, then go to 0
  a_count_inc:        assert property (@cb (count!=8'd200) |=> (count == $past(count)+8'd1));
  a_count_reset_200:  assert property (@cb (count==8'd200) |=> (count == 8'd0));

  // WR_n toggles only at count==20 and count==200
  a_wr_toggle_20:     assert property (@cb (count==8'd20)  |=> (WR_n != $past(WR_n)));
  a_wr_toggle_200:    assert property (@cb (count==8'd200) |=> (WR_n != $past(WR_n)));
  a_wr_stable_other:  assert property (@cb !(count inside {8'd20,8'd200}) |=> (WR_n == $past(WR_n)));

  // Coverage
  c_toggle_at_20:     cover property (@cb reset_n && (count==8'd20)  |=> $changed(WR_n));
  c_toggle_at_200:    cover property (@cb reset_n && (count==8'd200) |=> $changed(WR_n));
  c_full_cycle:       cover property (@cb $rose(reset_n)
                                      ##[1:$] (count==8'd20)  ##1 $changed(WR_n)
                                      ##[1:$] (count==8'd200) ##1 $changed(WR_n)
                                      ##[1:$] (count==8'd20)  ##1 $changed(WR_n));

endmodule

// Bind into DUT
bind ADCinterface ADCinterface_sva u_adcinterface_sva(
  .clk    (clk),
  .reset_n(reset_n),
  .CS_n   (CS_n),
  .RD_n   (RD_n),
  .WR_n   (WR_n),
  .count  (count)
);