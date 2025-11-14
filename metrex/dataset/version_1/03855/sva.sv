// SVA for NIOS_SYSTEMV3_NIOS_CPU_nios2_oci_im
// Bind into DUT or include alongside
bind NIOS_SYSTEMV3_NIOS_CPU_nios2_oci_im nios2_oci_im_sva i_nios2_oci_im_sva
(
  .* // relies on identical port names
);

module nios2_oci_im_sva (
  input clk,
  input [37:0] jdo,
  input jrst_n,
  input reset_n,
  input take_action_tracectrl,
  input take_action_tracemem_a,
  input take_action_tracemem_b,
  input take_no_action_tracemem_a,
  input [15:0] trc_ctrl,
  input [35:0] tw,
  input tracemem_on,
  input [35:0] tracemem_trcdata,
  input tracemem_tw,
  input trc_enb,
  input [6:0] trc_im_addr,
  input trc_wrap,
  input xbrk_wrap_traceoff
);

  default clocking cb @(posedge clk); endclocking

  // Helpers
  wire trc_on_chip_sva = ~trc_ctrl[8];
  wire tw_valid_sva    = |tw[35:32];
  wire no_action       = !take_action_tracectrl && !take_action_tracemem_a && !take_action_tracemem_b && !take_no_action_tracemem_a;
  wire act_ctrl        = take_action_tracectrl && (jdo[4] || jdo[3]);
  wire inc_sel         = (trc_enb && trc_on_chip_sva && tw_valid_sva) && !no_action && !act_ctrl;
  wire none_sel        = !no_action && !act_ctrl && !(trc_enb && trc_on_chip_sva && tw_valid_sva);

  // past-valid guards per reset domain
  logic past_n, past_j;
  always_ff @(posedge clk or negedge reset_n) if (!reset_n) past_n <= 1'b0; else past_n <= 1'b1;
  always_ff @(posedge clk or negedge jrst_n) if (!jrst_n)   past_j <= 1'b0; else past_j <= 1'b1;

  // Async jrst_n domain: trc_im_addr/trc_wrap
  assert property (!jrst_n |-> (trc_im_addr==7'd0 && trc_wrap==1'b0));
  assert property (past_j && jrst_n && no_action |=> (trc_im_addr==7'd0 && trc_wrap==1'b0));
  assert property (past_j && jrst_n && take_action_tracectrl && jdo[4] |=> trc_im_addr==7'd0);
  assert property (past_j && jrst_n && take_action_tracectrl && jdo[3] |=> trc_wrap==1'b0);
  assert property (past_j && jrst_n && inc_sel |=> trc_im_addr == $past(trc_im_addr) + 7'd1);
  assert property (past_j && jrst_n && inc_sel && $past(&trc_im_addr) |=> (trc_im_addr==7'd0 && trc_wrap==1'b1));
  assert property (past_j && jrst_n && inc_sel && !$past(&trc_im_addr) |=> trc_wrap == $past(trc_wrap));
  assert property (past_j && jrst_n && none_sel |=> (trc_im_addr==$past(trc_im_addr) && trc_wrap==$past(trc_wrap)));

  // reset_n domain: trc_enb/tracemem/xbrk
  assert property (!reset_n |-> (trc_enb==1'b0 && tracemem_on==1'b0 && tracemem_trcdata==36'd0 && tracemem_tw==1'b0 && xbrk_wrap_traceoff==1'b0));
  assert property (past_n && reset_n |-> trc_enb == $past(trc_ctrl[0]));
  assert property (past_n && reset_n |-> tracemem_on == $past(trc_enb));
  assert property (past_n && reset_n && $past(trc_enb && tw_valid_sva) |-> tracemem_trcdata == $past(tw));
  assert property (past_n && reset_n && !$past(trc_enb && tw_valid_sva) |-> tracemem_trcdata == $past(tracemem_trcdata));
  assert property (past_n && reset_n |-> tracemem_tw == $past(trc_wrap));
  assert property (past_n && reset_n |-> xbrk_wrap_traceoff == $past(trc_ctrl[10] & trc_wrap));

  // Sanity on derived terms (combinational intent)
  assert property (1'b1 |-> trc_on_chip_sva == ~trc_ctrl[8]);
  assert property (1'b1 |-> tw_valid_sva == (|tw[35:32]));

  // Key coverage
  cover property (past_j && jrst_n && no_action);
  cover property (past_j && jrst_n && take_action_tracectrl && jdo[4]);
  cover property (past_j && jrst_n && take_action_tracectrl && jdo[3]);
  cover property (past_j && jrst_n && inc_sel);
  cover property (past_j && jrst_n && inc_sel && $past(&trc_im_addr));
  cover property (past_n && reset_n && $rose(trc_enb));
  cover property (past_n && reset_n && $past(trc_enb && tw_valid_sva));
  cover property (past_n && reset_n && xbrk_wrap_traceoff);
  cover property (past_j && jrst_n && (trc_enb && !trc_on_chip_sva && tw_valid_sva)); // on-chip disabled while traffic present

endmodule