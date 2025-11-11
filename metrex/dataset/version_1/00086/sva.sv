// SVA for debug_lsa: concise, high-value checks and coverage.
// Drop this in a bind file or include and bind to the DUT.

`ifndef DEBUG_LSA_SVA
`define DEBUG_LSA_SVA

bind debug_lsa debug_lsa_sva();

module debug_lsa_sva;

  // ----------------------------
  // av_clk domain assertions
  // ----------------------------

  // sync_av update rule (increment only when echoed equal; otherwise hold)
  assert property (@(posedge av_clk) disable iff (av_rst)
    (sync_lsa_av == $past(sync_av)) |-> (sync_av == $past(sync_av) + 2'd1));

  assert property (@(posedge av_clk) disable iff (av_rst)
    (sync_lsa_av != $past(sync_av)) |-> (sync_av == $past(sync_av)));

  // Crossed snapshots only change on handshake cycle
  assert property (@(posedge av_clk) disable iff (av_rst)
    (sync_av != 2'b01) |-> $stable({av_live, av_running, av_done, av_mode, av_force, av_arm}));

  // Readdatavalid is 1-cycle pipeline of av_read
  assert property (@(posedge av_clk) disable iff (av_rst)
    av_readdatavalid == $past(av_read));

  // Readback data correctness
  assert property (@(posedge av_clk) disable iff (av_rst)
    $past(av_read) && ($past(av_address)==10'd0)
      |-> av_readdata == {16'd0, ctrl_mode, 4'd0, av_running, av_done, ctrl_force, ctrl_arm});

  assert property (@(posedge av_clk) disable iff (av_rst)
    $past(av_read) && ($past(av_address)==10'd1)
      |-> av_readdata == av_live);

  assert property (@(posedge av_clk) disable iff (av_rst)
    $past(av_read) && ($past(av_address) inside {[10'd2:10'd1023]})
      |-> av_readdata == sample_data[$past(av_address)]);

  // Control regs: reset/init/write semantics
  assert property (@(posedge av_clk)
    av_rst |-> (ctrl_arm==1'b0 && ctrl_force==1'b0 && ctrl_mode==8'd0 && init_cycle==1'b0));

  assert property (@(posedge av_clk) disable iff (av_rst)
    $past(init_cycle)==1'b0 |-> (ctrl_arm==(INIT_ARMED!=0) &&
                                 ctrl_force==(INIT_FORCED!=0) &&
                                 ctrl_mode==INIT_MODE &&
                                 init_cycle==1'b1));

  assert property (@(posedge av_clk) disable iff (av_rst)
    $past(init_cycle) && !$past(av_write && av_address==10'd0)
      |-> $stable({ctrl_arm, ctrl_force, ctrl_mode}));

  assert property (@(posedge av_clk) disable iff (av_rst)
    $past(av_write && (av_address==10'd0))
      |-> (ctrl_arm  == $past(av_writedata[0])   &&
           ctrl_force== $past(av_writedata[1])   &&
           ctrl_mode == $past(av_writedata[15:8])));


  // ----------------------------
  // lsa_clk domain assertions
  // ----------------------------

  // Running flag tied to MSB of write address
  assert property (@(posedge lsa_clk) sample_running == sample_waddr[10]);

  // sample_waddr FSM next-state rules
  assert property (@(posedge lsa_clk)
    !$past(lsa_arm) |-> (sample_waddr == 11'h001));

  assert property (@(posedge lsa_clk)
    $past(lsa_arm) && !$past(sample_waddr[10]) && (|$past(sample_waddr[9:0]))
      |-> (sample_waddr == $past(sample_waddr) + 11'd1));

  assert property (@(posedge lsa_clk)
    $past(lsa_arm) && ($past(sample_waddr)==11'h400) && !$past(lsa_force || lsa_trigger)
      |-> (sample_waddr == 11'h400));

  assert property (@(posedge lsa_clk)
    $past(lsa_arm) && ($past(sample_waddr)==11'h400) &&  $past(lsa_force || lsa_trigger)
      |-> (sample_waddr == 11'h401));

  assert property (@(posedge lsa_clk)
    $past(lsa_arm) &&
    ($past(sample_waddr)!=11'h000) &&
    !((!$past(sample_waddr[10]) && (|$past(sample_waddr[9:0]))) || ($past(sample_waddr)==11'h400))
      |-> (sample_waddr == $past(sample_waddr) + 11'd1));

  assert property (@(posedge lsa_clk)
    $past(lsa_arm) && ($past(sample_waddr)==11'h000)
      |-> (sample_waddr == 11'h000)); // sticky at 0 until disarmed

  // Done flag exact definition
  assert property (@(posedge lsa_clk)
    sample_done == (lsa_arm && (sample_waddr==11'h000)));

  // Memory write semantics: every armed cycle writes current index
  assert property (@(posedge lsa_clk)
    $past(lsa_arm)
      |-> (sample_data[$past(sample_waddr[9:0])]
             == ($past(sample_waddr[10]) ? $past(lsa_data) : 32'd0)));

  // Crossed-to-LSA regs only update on handshake cycle
  assert property (@(posedge lsa_clk)
    (sync_lsa != 2'b10) |-> $stable({lsa_live, lsa_running, lsa_done, lsa_mode, lsa_force, lsa_arm}));


  // ----------------------------
  // Key coverage
  // ----------------------------

  // Handshake states seen
  cover property (@(posedge av_clk)  disable iff (av_rst) sync_av  == 2'b01);
  cover property (@(posedge lsa_clk)                          sync_lsa== 2'b10);

  // Control path exercised
  cover property (@(posedge av_clk)  disable iff (av_rst) av_write && (av_address==10'd0));

  // Read paths exercised
  cover property (@(posedge av_clk)  disable iff (av_rst) av_read && (av_address==10'd0));
  cover property (@(posedge av_clk)  disable iff (av_rst) av_read && (av_address==10'd1));
  cover property (@(posedge av_clk)  disable iff (av_rst) av_read && (av_address inside {[10'd2:10'd1023]}));

  // Capture completes via trigger
  cover property (@(posedge lsa_clk)
    lsa_arm && (sample_waddr==11'h400) ##1 lsa_trigger ##1 (sample_waddr==11'h401)
      ##[1:1200] (sample_waddr==11'h000 && sample_done));

  // Capture completes via force
  cover property (@(posedge lsa_clk)
    lsa_arm && (sample_waddr==11'h400) ##1 lsa_force ##1 (sample_waddr==11'h401)
      ##[1:1200] (sample_waddr==11'h000 && sample_done));

endmodule

`endif // DEBUG_LSA_SVA