// SVA for processing_system7_v5_3_w_atc
// Place inside the module or bind with hierarchical paths to internal signals.

`ifndef ATC_SVA
`define ATC_SVA

// synthesis translate_off
// pragma coverage off

// Default clocking/reset
default clocking cb @(posedge ACLK); endclocking
default disable iff (ARESET);

// -----------------------------------------------------------------------------
// Combinational equivalences (sanity of assigns)
// -----------------------------------------------------------------------------
assert property (any_strb_deasserted == (S_AXI_WSTRB != {C_AXI_DATA_WIDTH/8{1'b1}}));
assert property (incoming_strb_issue == (cmd_w_valid & S_AXI_WVALID & cmd_w_check & any_strb_deasserted));

assert property (data_pop == (S_AXI_WVALID & M_AXI_WREADY & cmd_w_valid & ~cmd_b_full & ~cmd_b_push_blocked));
assert property (cmd_b_push_blocked == (cmd_b_push_i & cmd_b_full));
assert property (cmd_b_push == (cmd_b_push_i & ~cmd_b_full));

assert property (M_AXI_WVALID == (S_AXI_WVALID & cmd_w_valid & ~cmd_b_full & ~cmd_b_push_blocked));
assert property (S_AXI_WREADY == (M_AXI_WREADY & cmd_w_valid & ~cmd_b_full & ~cmd_b_push_blocked));
assert property (cmd_w_ready == (data_pop & S_AXI_WLAST));

assert property (cmd_b_error == strb_issue);

// Data path passthrough
assert property (M_AXI_WID   == S_AXI_WID);
assert property (M_AXI_WDATA == S_AXI_WDATA);
assert property (M_AXI_WSTRB == S_AXI_WSTRB);
assert property (M_AXI_WLAST == S_AXI_WLAST);
assert property (M_AXI_WUSER == S_AXI_WUSER);

// Handshake consistency
assert property (data_pop == (M_AXI_WVALID & M_AXI_WREADY));
assert property (M_AXI_WVALID |-> (S_AXI_WVALID && cmd_w_valid && !cmd_b_full && !cmd_b_push_blocked));
assert property ((S_AXI_WVALID && cmd_w_valid && !cmd_b_full && !cmd_b_push_blocked) |-> M_AXI_WVALID);

// cmd_b_full gating
assert property (cmd_b_full |-> !cmd_b_push);
assert property (cmd_b_push_i && !cmd_b_full |-> cmd_b_push);
assert property (cmd_b_push_i &&  cmd_b_full |-> cmd_b_push_blocked);

// -----------------------------------------------------------------------------
// Sequential register behaviors
// -----------------------------------------------------------------------------

// Reset values (one cycle after ARESET high)
assert property (ARESET |=> (first_word && (strb_issue==1'b0) && (cmd_b_id=={C_AXI_ID_WIDTH{1'b0}}) && (cmd_b_push_i==1'b0)));

// first_word update
assert property (data_pop |=> first_word == $past(S_AXI_WLAST));
assert property (!data_pop |=> first_word == $past(first_word));

// strb_issue accumulation
assert property (data_pop && first_word |=> strb_issue == $past(incoming_strb_issue));
assert property (data_pop && !first_word |=> strb_issue == ($past(incoming_strb_issue) | $past(strb_issue)));

// cmd_b_id capture on data_pop
assert property (data_pop |=> cmd_b_id == $past(cmd_w_id));

// cmd_b_push_i next-state definition
assert property (!ARESET |=> cmd_b_push_i == $past((S_AXI_WLAST & data_pop) | cmd_b_push_blocked));

// After accepting WLAST, push will occur when not full
assert property ((S_AXI_WLAST && data_pop) ##1 (!cmd_b_full)[*0:$] ##1 (!cmd_b_full) |-> cmd_b_push);

// -----------------------------------------------------------------------------
// Functional coverage
// -----------------------------------------------------------------------------

// Cover: clean multi-beat burst with no strobe issues, immediate push
cover property (
  first_word && data_pop && !S_AXI_WLAST &&
  (!incoming_strb_issue)[*1:$] ##1 (data_pop && S_AXI_WLAST && !incoming_strb_issue) ##1
  (cmd_b_push && !cmd_b_error && cmd_w_ready)
);

// Cover: burst with strobe issue somewhere (not first), error flagged on push
cover property (
  first_word && data_pop && !S_AXI_WLAST && !incoming_strb_issue
  ##1 (!first_word && data_pop && !S_AXI_WLAST && incoming_strb_issue)
  ##[0:$] (data_pop && S_AXI_WLAST)
  ##1 (cmd_b_push && cmd_b_error)
);

// Cover: push blocked by full, then released
cover property (
  (data_pop && S_AXI_WLAST)
  ##1 (cmd_b_full && cmd_b_push_blocked)[*1:$]
  ##1 (!cmd_b_full && cmd_b_push)
);

// Cover: backpressure stops data_pop (WVALID high but M ready low), later proceeds
cover property (
  (S_AXI_WVALID && cmd_w_valid && !cmd_b_full && !cmd_b_push_blocked && !M_AXI_WREADY)
  ##[1:$] (M_AXI_WREADY && data_pop)
);

// pragma coverage on
// synthesis translate_on
`endif