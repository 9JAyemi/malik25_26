// SVA for qmem_bridge
// Bind into DUT to check protocol, state machine, CDC handshakes, and data/addr/sel mapping.

module qmem_bridge_sva #(
  parameter MAW = 22,
  parameter MSW = 4,
  parameter MDW = 32,
  parameter SAW = 22,
  parameter SSW = 2,
  parameter SDW = 16
) (qmem_bridge dut);

  // Local view of DUT signals
  wire                 m_clk       = dut.m_clk;
  wire                 s_clk       = dut.s_clk;
  wire [2:0]           state       = dut.state;
  wire [2:0]           cs_sync     = dut.cs_sync;
  wire [1:0]           s_ack_sync  = dut.s_ack_sync;
  wire [2:0]           m_ack_sync  = dut.m_ack_sync;
  wire                 done        = dut.done;
  wire                 s_ack       = dut.s_ack;
  wire                 m_ack       = dut.m_ack;
  wire                 m_err       = dut.m_err;

  wire [MAW-1:0]       adr_d       = dut.adr_d;
  wire                 we_d        = dut.we_d;
  wire [MSW-1:0]       sel_d       = dut.sel_d;
  wire [MDW-1:0]       dat_w_d     = dut.dat_w_d;

  wire [SAW-1:0]       s_adr       = dut.s_adr;
  wire                 s_cs        = dut.s_cs;
  wire                 s_we        = dut.s_we;
  wire [SSW-1:0]       s_sel       = dut.s_sel;
  wire [SDW-1:0]       s_dat_w     = dut.s_dat_w;
  wire [SDW-1:0]       s_dat_r     = dut.s_dat_r;
  wire [MDW-1:0]       m_dat_r     = dut.m_dat_r;

  // State encoding from DUT
  localparam ST_IDLE    = 3'b000;
  localparam ST_U_SETUP = 3'b010;
  localparam ST_U_WAIT  = 3'b011;
  localparam ST_L_SETUP = 3'b100;
  localparam ST_L_WAIT  = 3'b101;
  localparam ST_A_WAIT  = 3'b111;

  // 1) Basic state legality
  assert property (@(posedge s_clk) 1'b1 |-> state inside {ST_IDLE,ST_U_SETUP,ST_U_WAIT,ST_L_SETUP,ST_L_WAIT,ST_A_WAIT});

  // 2) IDLE entry condition and transition
  assert property (@(posedge s_clk) (state==ST_IDLE && cs_sync[2]) |=> state==ST_U_SETUP);
  assert property (@(posedge s_clk) (state==ST_IDLE && !cs_sync[2]) |-> $stable(state));

  // 3) U half setup semantics
  assert property (@(posedge s_clk) (state==ST_U_SETUP) |-> s_cs && s_we==we_d && s_sel==sel_d[MSW-1 -: SSW] &&
                                                  s_dat_w==dat_w_d[MDW-1 -: SDW] &&
                                                  s_adr[SAW-1:2]==adr_d[MAW-1:2] && s_adr[1:0]==2'b00);
  assert property (@(posedge s_clk) (state==ST_U_SETUP) |=> state==ST_U_WAIT);

  // 4) U half wait behavior
  assert property (@(posedge s_clk) (state==ST_U_WAIT && !s_ack) |-> s_cs && $stable(s_adr) && $stable(s_we) && $stable(s_sel));
  assert property (@(posedge s_clk) (state==ST_U_WAIT && s_ack)  |-> !s_cs);
  assert property (@(posedge s_clk) (state==ST_U_WAIT && s_ack)  |=> state==ST_L_SETUP);

  // 5) L half setup semantics
  assert property (@(posedge s_clk) (state==ST_L_SETUP) |-> s_cs && s_we==we_d && s_sel==sel_d[SSW-1:0] &&
                                                  s_dat_w==dat_w_d[SDW-1:0] &&
                                                  s_adr[SAW-1:2]==adr_d[MAW-1:2] && s_adr[1:0]==2'b10);
  assert property (@(posedge s_clk) (state==ST_L_SETUP) |=> state==ST_L_WAIT);

  // 6) L half wait behavior and done protocol
  assert property (@(posedge s_clk) (state==ST_L_WAIT && !s_ack) |-> s_cs && $stable(s_adr) && $stable(s_we) && $stable(s_sel));
  assert property (@(posedge s_clk) (state==ST_L_WAIT && s_ack)  |-> !s_cs);
  assert property (@(posedge s_clk) (state==ST_L_WAIT && s_ack)  |=> state==ST_A_WAIT && done);

  // 7) A_WAIT behavior and return to IDLE
  assert property (@(posedge s_clk) (state==ST_A_WAIT && !s_ack_sync[1]) |-> done);
  assert property (@(posedge s_clk) (state==ST_A_WAIT && s_ack_sync[1])  |=> state==ST_IDLE && !done);

  // 8) s_cs only during active halves; s_adr[0] is always 0 when active
  assert property (@(posedge s_clk) s_cs |-> state inside {ST_U_SETUP,ST_U_WAIT,ST_L_SETUP,ST_L_WAIT} && s_adr[0]==1'b0);

  // 9) Capture of master request fields when cs_sync[1] is high
  assert property (@(posedge s_clk) cs_sync[1] |=> adr_d==$past(dut.m_adr) && we_d==$past(dut.m_we) &&
                                                sel_d==$past(dut.m_sel) && dat_w_d==$past(dut.m_dat_w));

  // 10) Read data assembly from two 16-bit slave reads
  assert property (@(posedge s_clk) (state==ST_U_WAIT && s_ack) |=> m_dat_r[MDW-1:SDW] == $past(s_dat_r));
  assert property (@(posedge s_clk) (state==ST_L_WAIT && s_ack) |=> m_dat_r[SDW-1:0]   == $past(s_dat_r));

  // 11) Lower half never precedes upper; A_WAIT only after lower
  assert property (@(posedge s_clk) state==ST_L_SETUP |-> $past(state)==ST_U_WAIT);
  assert property (@(posedge s_clk) state==ST_A_WAIT  |-> $past(state)==ST_L_WAIT);

  // 12) m_ack pulse is single-cycle on m_clk
  assert property (@(posedge m_clk) m_ack |-> !$past(m_ack) && ##1 !m_ack);

  // 13) m_err must remain 0
  assert property (@(posedge m_clk) m_err==1'b0);

  // 14) Cover: one full READ transaction (we_d==0)
  cover property (@(posedge s_clk)
    state==ST_IDLE ##1 cs_sync[2] ##1
    state==ST_U_SETUP && !we_d ##1
    state==ST_U_WAIT ##[1:$] s_ack ##1
    state==ST_L_SETUP && !we_d ##1
    state==ST_L_WAIT  ##[1:$] s_ack ##1
    state==ST_A_WAIT  ##[1:$] s_ack_sync[1] ##1
    state==ST_IDLE
  );

  // 15) Cover: one full WRITE transaction (we_d==1)
  cover property (@(posedge s_clk)
    state==ST_IDLE ##1 cs_sync[2] ##1
    state==ST_U_SETUP && we_d ##1
    state==ST_U_WAIT  ##[1:$] s_ack ##1
    state==ST_L_SETUP && we_d ##1
    state==ST_L_WAIT  ##[1:$] s_ack ##1
    state==ST_A_WAIT  ##[1:$] s_ack_sync[1] ##1
    state==ST_IDLE
  );

  // 16) Cover: both halves acknowledge in back-to-back cycles
  cover property (@(posedge s_clk)
    state==ST_U_WAIT && s_ack ##1 state==ST_L_WAIT && s_ack
  );

endmodule

bind qmem_bridge qmem_bridge_sva #(.MAW(MAW),.MSW(MSW),.MDW(MDW),.SAW(SAW),.SSW(SSW),.SDW(SDW)) qmem_bridge_sva_i(.dut(this));