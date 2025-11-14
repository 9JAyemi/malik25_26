// SVA for contador_AD_MES_2dig
// Concise, high-quality checks + coverage
bind contador_AD_MES_2dig contador_AD_MES_2dig_sva sva();

module contador_AD_MES_2dig_sva;

  // Access bound instance signals directly
  // clk, reset, en_count, enUP, enDOWN, data_MES
  // q_act, digit1, digit0, count_data

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset)

  // Basic sanity
  a_known:      assert property (!$isunknown({en_count,enUP,enDOWN,q_act,digit1,digit0,count_data,data_MES}));
  a_range:      assert property (q_act inside {[4'd0:4'd11]});

  // Hold when not enabled to count
  a_hold_dis:   assert property (!(en_count==4'd5 && (enUP || enDOWN)) |=> $stable(q_act));

  // UP behavior (also covers simultaneous enUP&enDOWN due to priority)
  a_up:         assert property ((en_count==4'd5 && enUP) |=> 
                                 q_act == (($past(q_act)>=4'd11)? 4'd0 : $past(q_act)+4'd1));

  // DOWN behavior only when enUP is low
  a_down:       assert property ((en_count==4'd5 && !enUP && enDOWN) |=> 
                                 q_act == (($past(q_act)==4'd0)? 4'd11 : $past(q_act)-4'd1));

  // Explicitly check priority when both asserted
  a_prio:       assert property ((en_count==4'd5 && enUP && enDOWN) |=> 
                                 q_act == (($past(q_act)>=4'd11)? 4'd0 : $past(q_act)+4'd1));

  // Combinational derivations
  a_cnt_plus1:  assert property (count_data == (q_act + 4'd1));

  a_bcd_lo:     assert property ((q_act <= 4'd8)  |-> (digit1==4'd0 && digit0==(q_act+4'd1)));
  a_bcd_hi:     assert property ((q_act inside {[4'd9:4'd11]}) |-> (digit1==4'd1 && digit0==(q_act-4'd9)));

  a_concat:     assert property (data_MES == {digit1,digit0});

  // Reset holds counter at 0 on clocks while reset is high
  a_rst_hold:   assert property (reset |-> q_act==4'd0);

  // --------------------------------
  // Coverage
  // --------------------------------
  // Visit all 12 states
  genvar i;
  generate
    for (i=0;i<=11;i++) begin : C_STATES
      cover property (q_act == i[3:0]);
    end
  endgenerate

  // Observe both wrap events and priority case
  c_wrap_up:    cover property (q_act==4'd11 ##1 (en_count==4'd5 && enUP) ##1 q_act==4'd0);
  c_wrap_down:  cover property (q_act==4'd0  ##1 (en_count==4'd5 && !enUP && enDOWN) ##1 q_act==4'd11);
  c_both_prio:  cover property ((en_count==4'd5 && enUP && enDOWN) ##1 $changed(q_act));

  // See all 12 BCD outputs on data_MES
  cover property (data_MES==8'h01);
  cover property (data_MES==8'h02);
  cover property (data_MES==8'h03);
  cover property (data_MES==8'h04);
  cover property (data_MES==8'h05);
  cover property (data_MES==8'h06);
  cover property (data_MES==8'h07);
  cover property (data_MES==8'h08);
  cover property (data_MES==8'h09);
  cover property (data_MES==8'h10);
  cover property (data_MES==8'h11);
  cover property (data_MES==8'h12);

endmodule