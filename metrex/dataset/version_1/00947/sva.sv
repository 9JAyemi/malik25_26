Below is a concise, high‑value SVA block you can paste inside the module (e.g., at the end). It checks the CDC toggle protocol, Wishbone handshake relationships on both sides, data capture discipline, basic safety invariants, and provides targeted coverage. It also includes minimal environment assumptions that classic Wishbone masters/slaves keep STB asserted until ACK and do not ACK when STB=0.

`ifndef SYNTHESIS
// pragma translate_off

// -------------------------------------
// Assertions and coverage for wb_abrg
// -------------------------------------
logic [31:0] req_cnt, ack_cnt;

// Count requests/acks in the wbm clock domain
always @(posedge wbm_clk_i or posedge sys_rst) begin
  if (sys_rst) begin
    req_cnt <= '0;
    ack_cnt <= '0;
  end else begin
    if ($rose(wbm_stb_o)) req_cnt <= req_cnt + 1;
    if ($rose(wbm_ack_i)) ack_cnt <= ack_cnt + 1;
  end
end

// Basic WB master side relations
assert property (@(posedge wbm_clk_i) disable iff (sys_rst)
  wbm_cyc_o == wbm_stb_o);

// STB holds until ACK, and drops after ACK
assert property (@(posedge wbm_clk_i) disable iff (sys_rst)
  (wbm_stb_o && !wbm_ack_i) |=> wbm_stb_o);
assert property (@(posedge wbm_clk_i) disable iff (sys_rst)
  (wbm_stb_o && wbm_ack_i) |=> !wbm_stb_o);

// New request only starts from sync pulse
assert property (@(posedge wbm_clk_i) disable iff (sys_rst)
  $rose(wbm_stb_o) |-> (sync_stb[2] ^ sync_stb[1]));

// No ACK without active STB (env + design contract)
assert property (@(posedge wbm_clk_i) disable iff (sys_rst)
  wbm_ack_i |-> wbm_stb_o);

// Toggle generators behave as intended
assert property (@(posedge wbs_clk_i) disable iff (sys_rst)
  init_tr |-> (ft_stb != $past(ft_stb)));
assert property (@(posedge wbs_clk_i) disable iff (sys_rst)
  !init_tr |-> $stable(ft_stb));

assert property (@(posedge wbm_clk_i) disable iff (sys_rst)
  wbm_ack_i |-> (ft_ack != $past(ft_ack)));
assert property (@(posedge wbm_clk_i) disable iff (sys_rst)
  !wbm_ack_i |-> $stable(ft_ack));

// Synchronizer shift correctness
assert property (@(posedge wbm_clk_i) disable iff (sys_rst)
  sync_stb == { $past(sync_stb[1:0]), ft_stb });
assert property (@(posedge wbs_clk_i) disable iff (sys_rst)
  sync_ack == { $past(sync_ack[1:0]), ft_ack });

// WBS ACK only when WBS STB is asserted (Wishbone contract)
assert property (@(posedge wbs_clk_i) disable iff (sys_rst)
  $rose(wbs_ack_o) |-> (wbs_stb_i & wbs_cyc_i));

// WBS ACK should be a pulse (no multi-cycle high)
assert property (@(posedge wbs_clk_i) disable iff (sys_rst)
  !(wbs_ack_o && $past(wbs_ack_o)));

// Outstanding tracking: at most one in flight, no over-ack
assert property (@(posedge wbm_clk_i) disable iff (sys_rst)
  ack_cnt <= req_cnt);
assert property (@(posedge wbm_clk_i) disable iff (sys_rst)
  (req_cnt - ack_cnt) <= 1);

// Data capture discipline
assert property (@(posedge wbm_clk_i) disable iff (sys_rst)
  !wbm_ack_i |-> $stable(wbm_dat_i_r));
// Pipeline moves as coded (structural checks)
assert property (@(posedge wbm_clk_i) disable iff (sys_rst)
  {wbm_adr_o, wbm_adr_o_r} == { $past(wbm_adr_o_r), wbs_adr_i });
assert property (@(posedge wbm_clk_i) disable iff (sys_rst)
  {wbm_dat_o, wbm_dat_o_r} == { $past(wbm_dat_o_r), wbs_dat_i });
assert property (@(posedge wbm_clk_i) disable iff (sys_rst)
  {wbm_sel_o, wbm_sel_o_r} == { $past(wbm_sel_o_r), wbs_sel_i });
assert property (@(posedge wbm_clk_i) disable iff (sys_rst)
  {wbm_we_o,  wbm_we_o_r } == { $past(wbm_we_o_r ), wbs_we_i  });
assert property (@(posedge wbm_clk_i) disable iff (sys_rst)
  {wbm_tga_o, wbm_tga_o_r} == { $past(wbm_tga_o_r), wbs_tga_i });
assert property (@(posedge wbs_clk_i) disable iff (sys_rst)
  {wbs_dat_o, wbs_dat_o_r} == { $past(wbs_dat_o_r), wbm_dat_i_r });

// Knownness (no X) after reset deassertion
assert property (@(posedge wbm_clk_i) disable iff (sys_rst)
  !$isunknown({wbm_stb_o, wbm_cyc_o, wbm_adr_o, wbm_dat_o, wbm_sel_o, wbm_tga_o, wbm_we_o}));
assert property (@(posedge wbs_clk_i) disable iff (sys_rst)
  !$isunknown({wbs_ack_o, wbs_dat_o}));

// Minimal environment assumptions (Wishbone protocol)
// WBS side: Master holds STB until ACK
assume property (@(posedge wbs_clk_i) disable iff (sys_rst)
  (wbs_stb_i & wbs_cyc_i) |-> ((wbs_stb_i & wbs_cyc_i) until_with $rose(wbs_ack_o)));

// WBM side: Slave only ACKs when STB asserted
assume property (@(posedge wbm_clk_i) disable iff (sys_rst)
  wbm_ack_i |-> wbm_stb_o);

// Coverage
cover property (@(posedge wbm_clk_i)
  $rose(wbm_stb_o) ##[1:16] wbm_ack_i);

cover property (@(posedge wbm_clk_i)
  $rose(wbm_stb_o) ##[1:8] $rose(wbm_ack_i) ##1 $rose(wbm_stb_o) ##[1:8] $rose(wbm_ack_i)); // back-to-back

cover property (@(posedge wbs_clk_i)
  $rose(wbs_stb_i & wbs_cyc_i) ##[1:32] $rose(wbs_ack_o));

cover property (@(posedge wbs_clk_i)
  ($rose(wbs_stb_i & wbs_cyc_i) && !wbs_we_i) ##[1:32] $rose(wbs_ack_o) ##0 $changed(wbs_dat_o));

// pragma translate_on
`endif