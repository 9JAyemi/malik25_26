// SVA for k580wi53 (wrapper) and k580wi53channel (per-channel)
// Bind into DUT; concise checks + essential coverage

bind k580wi53 k580wi53_sva();
module k580wi53_sva;
  default clocking cb @(posedge clk); endclocking

  // odata mux correctness
  a_mux_00: assert property (addr==2'b00 |-> odata==odata0);
  a_mux_01: assert property (addr==2'b01 |-> odata==odata1);
  a_mux_10: assert property (addr==2'b10 |-> odata==odata2);
  a_mux_11: assert property (addr==2'b11 |-> odata==8'h00);

  // Channel addr bit equals &addr
  a_ch_addr: assert property (ch0.addr == &addr && ch1.addr == &addr && ch2.addr == &addr);

  // Only one channel read or write-active at a time
  a_one_rd: assert property ($onehot0({ch0.rd, ch1.rd, ch2.rd}));
  a_one_we: assert property ($onehot0({~ch0.we_n, ~ch1.we_n, ~ch2.we_n}));

  // Direct per-address WE decode
  a_we_dir_00: assert property (!we_n && addr==2'b00 |-> ch0.we_n==1'b0 && ch1.we_n==1'b1 && ch2.we_n==1'b1);
  a_we_dir_01: assert property (!we_n && addr==2'b01 |-> ch1.we_n==1'b0 && ch0.we_n==1'b1 && ch2.we_n==1'b1);
  a_we_dir_10: assert property (!we_n && addr==2'b10 |-> ch2.we_n==1'b0 && ch0.we_n==1'b1 && ch1.we_n==1'b1);

  // Indirect WE via addr==2'b11 and idata[7:6]
  a_we_ind_00: assert property (!we_n && addr==2'b11 && idata[7:6]==2'b00 |-> ch0.we_n==1'b0 && ch1.we_n && ch2.we_n);
  a_we_ind_01: assert property (!we_n && addr==2'b11 && idata[7:6]==2'b01 |-> ch1.we_n==1'b0 && ch0.we_n && ch2.we_n);
  a_we_ind_10: assert property (!we_n && addr==2'b11 && idata[7:6]==2'b10 |-> ch2.we_n==1'b0 && ch0.we_n && ch1.we_n);

  // Read decode per address
  a_rd_decode_00: assert property (rd && addr==2'b00 |-> ch0.rd && !ch1.rd && !ch2.rd);
  a_rd_decode_01: assert property (rd && addr==2'b01 |-> ch1.rd && !ch0.rd && !ch2.rd);
  a_rd_decode_10: assert property (rd && addr==2'b10 |-> ch2.rd && !ch0.rd && !ch1.rd);

  // Minimal coverage
  c_rd_each:    cover property (rd && addr inside {2'b00,2'b01,2'b10});
  c_we_ind_all: cover property (!we_n && addr==2'b11 && idata[7:6] inside {2'b00,2'b01,2'b10});
endmodule


bind k580wi53channel k580wi53channel_sva();
module k580wi53channel_sva;
  default clocking cb @(posedge clk); endclocking

  // Read data mux correctness
  a_odata_00: assert property ({latched,ff}==2'b00 |-> odata==counter[7:0]);
  a_odata_01: assert property ({latched,ff}==2'b01 |-> odata==counter[15:8]);
  a_odata_10: assert property ({latched,ff}==2'b10 |-> odata==cntlatch[7:0]);
  a_odata_11: assert property ({latched,ff}==2'b11 |-> odata==cntlatch[15:8]);

  // Gate behavior
  a_gate_follow:  assert property ((gate != $past(gate)) && $past(mode[2:1]!=2'b01) |-> enabled==gate);
  a_gate_oneshot: assert property ($rose(gate) && $past(mode[2:1]==2'b01) |-> (enabled==1 && loaded==0));

  // RD falling edge side effects
  a_rd_ff_toggle:  assert property ($fell(rd) |-> (mode[5:4]==2'b11 ? ff == ~$past(ff) : ff == $past(ff)));
  a_rd_latch_clear: assert property ($fell(rd) && ($past(mode[5:4])!=2'b11 || $past(ff)) |-> latched==0);

  // WE falling edge @ control port (addr==1)
  a_we_ctl_latch: assert property ($fell(we_n) && addr && ($past(idata[5:4])==2'b00)
                                  |-> (cntlatch==$past(counter) && latched==1));
  a_we_ctl_mode:  assert property ($fell(we_n) && addr && ($past(idata[5:4])!=2'b00)
                                  |-> (mode==$past(idata[5:0]) && enabled==0 && loaded==0 && done==1
                                       && latched==0 && cout==($past(idata[3:1])!=3'b000)
                                       && ff==($past(idata[5:4])==2'b10)));

  // WE falling edge @ data port (addr==0), init/en/ff and common side-effects
  a_we_dat_01x: assert property ($fell(we_n) && !addr && $past(mode[5:4])==2'b01
                                |-> (init=={8'h00,$past(idata)} && enabled==gate && ff==0));
  a_we_dat_10x: assert property ($fell(we_n) && !addr && $past(mode[5:4])==2'b10
                                |-> (init=={$past(idata),8'h00} && enabled==gate && ff==1));
  a_we_dat_110: assert property ($fell(we_n) && !addr && $past(mode[5:4])==2'b11 && $past(ff)==0
                                |-> (init[7:0]==$past(idata) && enabled==0 && ff==1));
  a_we_dat_111: assert property ($fell(we_n) && !addr && $past(mode[5:4])==2'b11 && $past(ff)==1
                                |-> (init[15:8]==$past(idata) && enabled==gate && ff==0));
  a_we_dat_loaded_cout: assert property ($fell(we_n) && !addr
                                |-> (loaded==($past(mode[2:1])!=2'b00 && !$past(done))
                                     && cout==( ($past(mode[3:1])!=3'b000)
                                                || ($past(mode[5:4])==2'b01 && $past(idata)==8'b0000_0001) )));

  // Counting step (enabled and c rising)
  a_count_load_first: assert property ($rose(c) && $past(enabled) && !$past(loaded)
                                      |-> (counter==$past(init) && loaded==1 && first==1 && done==0
                                           && (($past(mode[3:2])==2'b00) -> (cout==0))));
  a_count_step_new:   assert property ($rose(c) && $past(enabled) && $past(loaded)
                                      && !($past(mode[2]) && ($past(newvalue)==16'h0000))
                                      |-> (counter==$past(newvalue) && first==0));
  a_count_reload:     assert property ($rose(c) && $past(enabled) && $past(loaded)
                                      && $past(mode[2]) && ($past(newvalue)==16'h0000)
                                      |-> (counter==$past(init) && first==($past(init[0]) & ~$past(cout))));

  // Terminal event cout/done updates (subset of casex table)
  a_term_0000: assert property ($rose(c) && $past(enabled) && $past(loaded)
                                && $past(newvalue[15:1]==15'b0) && !$past(done)
                                && $past({mode[3:1],newvalue[0]})==4'b0000
                                |-> ({cout,done}==2'b11));
  a_term_0010: assert property ($rose(c) && $past(enabled) && $past(loaded)
                                && $past(newvalue[15:1]==15'b0) && !$past(done)
                                && $past({mode[3:1],newvalue[0]})==4'b0010
                                |-> ({cout,done}==2'b11));
  a_term_1000: assert property ($rose(c) && $past(enabled) && $past(loaded)
                                && $past(newvalue[15:1]==15'b0) && !$past(done)
                                && $past({mode[3:1],newvalue[0]})==4'b1000
                                |-> ({cout,done}==2'b11));
  a_term_1010: assert property ($rose(c) && $past(enabled) && $past(loaded)
                                && $past(newvalue[15:1]==15'b0) && !$past(done)
                                && $past({mode[3:1],newvalue[0]})==4'b1010
                                |-> ({cout,done}==2'b11));

  // Minimal coverage
  c_ctl_each:     cover property ($fell(we_n) && addr && $past(idata[5:4]) inside {2'b00,2'b01,2'b10,2'b11});
  c_rd_toggle_ff: cover property ($fell(rd) && $past(mode[5:4]==2'b11));
  c_count_term:   cover property ($rose(c) && $past(enabled) && $past(loaded) && $past(newvalue[15:1]==15'b0));
endmodule