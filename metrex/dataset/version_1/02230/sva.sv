// SVA for NV_NVDLA_RT_csb2cacc
// Bind these assertions to the DUT

module NV_NVDLA_RT_csb2cacc_sva (
  input logic         nvdla_core_clk,
  input logic         nvdla_core_rstn,

  input logic         csb2cacc_req_src_pvld,
  input logic         csb2cacc_req_src_prdy,
  input logic [62:0]  csb2cacc_req_src_pd,

  input logic         cacc2csb_resp_src_valid,
  input logic [33:0]  cacc2csb_resp_src_pd,

  input logic         csb2cacc_req_dst_pvld,
  input logic [62:0]  csb2cacc_req_dst_pd,
  input logic         csb2cacc_req_dst_prdy,

  input logic         cacc2csb_resp_dst_valid,
  input logic [33:0]  cacc2csb_resp_dst_pd,

  // internal taps
  input logic         csb2cacc_req_pvld_d1,
  input logic         csb2cacc_req_pvld_d2,
  input logic         csb2cacc_req_pvld_d3,
  input logic [62:0]  csb2cacc_req_pd_d1,
  input logic [62:0]  csb2cacc_req_pd_d2,
  input logic [62:0]  csb2cacc_req_pd_d3,

  input logic         cacc2csb_resp_valid_d1,
  input logic         cacc2csb_resp_valid_d2,
  input logic         cacc2csb_resp_valid_d3,
  input logic [33:0]  cacc2csb_resp_pd_d1,
  input logic [33:0]  cacc2csb_resp_pd_d2,
  input logic [33:0]  cacc2csb_resp_pd_d3
);

  // Constant ready on source side
  assert property (@(posedge nvdla_core_clk) csb2cacc_req_src_prdy === 1'b1);

  // Reset drives outputs deasserted
  assert property (@(posedge nvdla_core_clk) !nvdla_core_rstn |-> (!csb2cacc_req_dst_pvld && !cacc2csb_resp_dst_valid));

  // No X on valids
  assert property (@(posedge nvdla_core_clk) disable iff (!nvdla_core_rstn) !$isunknown(csb2cacc_req_src_pvld));
  assert property (@(posedge nvdla_core_clk) disable iff (!nvdla_core_rstn) !$isunknown(csb2cacc_req_dst_pvld));
  assert property (@(posedge nvdla_core_clk) disable iff (!nvdla_core_rstn) !$isunknown(cacc2csb_resp_src_valid));
  assert property (@(posedge nvdla_core_clk) disable iff (!nvdla_core_rstn) !$isunknown(cacc2csb_resp_dst_valid));

  // Data known when valid
  assert property (@(posedge nvdla_core_clk) disable iff (!nvdla_core_rstn) csb2cacc_req_dst_pvld |-> !$isunknown(csb2cacc_req_dst_pd));
  assert property (@(posedge nvdla_core_clk) disable iff (!nvdla_core_rstn) cacc2csb_resp_dst_valid |-> !$isunknown(cacc2csb_resp_dst_pd));

  // End-to-end 3-cycle pipeline: request path
  assert property (@(posedge nvdla_core_clk) disable iff (!nvdla_core_rstn)
    csb2cacc_req_src_pvld |-> ##3 (csb2cacc_req_dst_pvld && (csb2cacc_req_dst_pd == $past(csb2cacc_req_src_pd,3)))
  );
  assert property (@(posedge nvdla_core_clk) disable iff (!nvdla_core_rstn)
    csb2cacc_req_dst_pvld |-> $past(csb2cacc_req_src_pvld,3)
  );

  // End-to-end 3-cycle pipeline: response path
  assert property (@(posedge nvdla_core_clk) disable iff (!nvdla_core_rstn)
    cacc2csb_resp_src_valid |-> ##3 (cacc2csb_resp_dst_valid && (cacc2csb_resp_dst_pd == $past(cacc2csb_resp_src_pd,3)))
  );
  assert property (@(posedge nvdla_core_clk) disable iff (!nvdla_core_rstn)
    cacc2csb_resp_dst_valid |-> $past(cacc2csb_resp_src_valid,3)
  );

  // Internal valid propagation (sanity of staging)
  assert property (@(posedge nvdla_core_clk) disable iff (!nvdla_core_rstn) csb2cacc_req_src_pvld |-> ##1 csb2cacc_req_pvld_d1);
  assert property (@(posedge nvdla_core_clk) disable iff (!nvdla_core_rstn) csb2cacc_req_pvld_d1   |-> ##1 csb2cacc_req_pvld_d2);
  assert property (@(posedge nvdla_core_clk) disable iff (!nvdla_core_rstn) csb2cacc_req_pvld_d2   |-> ##1 csb2cacc_req_pvld_d3);

  assert property (@(posedge nvdla_core_clk) disable iff (!nvdla_core_rstn) cacc2csb_resp_src_valid |-> ##1 cacc2csb_resp_valid_d1);
  assert property (@(posedge nvdla_core_clk) disable iff (!nvdla_core_rstn) cacc2csb_resp_valid_d1   |-> ##1 cacc2csb_resp_valid_d2);
  assert property (@(posedge nvdla_core_clk) disable iff (!nvdla_core_rstn) cacc2csb_resp_valid_d2   |-> ##1 cacc2csb_resp_valid_d3);

  // Internal data moves only when prior stage valid
  assert property (@(posedge nvdla_core_clk) disable iff (!nvdla_core_rstn)
    csb2cacc_req_pvld_d1 |-> (csb2cacc_req_pd_d1 == $past(csb2cacc_req_src_pd))
  );
  assert property (@(posedge nvdla_core_clk) disable iff (!nvdla_core_rstn)
    csb2cacc_req_pvld_d2 |-> (csb2cacc_req_pd_d2 == $past(csb2cacc_req_pd_d1))
  );
  assert property (@(posedge nvdla_core_clk) disable iff (!nvdla_core_rstn)
    csb2cacc_req_pvld_d3 |-> (csb2cacc_req_pd_d3 == $past(csb2cacc_req_pd_d2))
  );

  assert property (@(posedge nvdla_core_clk) disable iff (!nvdla_core_rstn)
    cacc2csb_resp_valid_d1 |-> (cacc2csb_resp_pd_d1 == $past(cacc2csb_resp_src_pd))
  );
  assert property (@(posedge nvdla_core_clk) disable iff (!nvdla_core_rstn)
    cacc2csb_resp_valid_d2 |-> (cacc2csb_resp_pd_d2 == $past(cacc2csb_resp_pd_d1))
  );
  assert property (@(posedge nvdla_core_clk) disable iff (!nvdla_core_rstn)
    cacc2csb_resp_valid_d3 |-> (cacc2csb_resp_pd_d3 == $past(cacc2csb_resp_pd_d2))
  );

  // Outputs mirror stage-3
  assert property (@(posedge nvdla_core_clk)
    (csb2cacc_req_dst_pvld == csb2cacc_req_pvld_d3) && (csb2cacc_req_dst_pd == csb2cacc_req_pd_d3)
  );
  assert property (@(posedge nvdla_core_clk)
    (cacc2csb_resp_dst_valid == cacc2csb_resp_valid_d3) && (cacc2csb_resp_dst_pd == cacc2csb_resp_pd_d3)
  );

  // Coverage: single, burst, and gap patterns propagate across 3-cycle latency
  cover property (@(posedge nvdla_core_clk) disable iff (!nvdla_core_rstn)
    csb2cacc_req_src_pvld ##3 csb2cacc_req_dst_pvld
  );
  cover property (@(posedge nvdla_core_clk) disable iff (!nvdla_core_rstn)
    csb2cacc_req_src_pvld [*4] ##3 csb2cacc_req_dst_pvld [*4]
  );
  cover property (@(posedge nvdla_core_clk) disable iff (!nvdla_core_rstn)
    csb2cacc_req_src_pvld ##1 !csb2cacc_req_src_pvld [*2] ##1 csb2cacc_req_src_pvld ##3
    csb2cacc_req_dst_pvld ##1 !csb2cacc_req_dst_pvld [*2] ##1 csb2cacc_req_dst_pvld
  );

  cover property (@(posedge nvdla_core_clk) disable iff (!nvdla_core_rstn)
    cacc2csb_resp_src_valid ##3 cacc2csb_resp_dst_valid
  );
  cover property (@(posedge nvdla_core_clk) disable iff (!nvdla_core_rstn)
    cacc2csb_resp_src_valid [*4] ##3 cacc2csb_resp_dst_valid [*4]
  );
  cover property (@(posedge nvdla_core_clk) disable iff (!nvdla_core_rstn)
    cacc2csb_resp_src_valid ##1 !cacc2csb_resp_src_valid [*2] ##1 cacc2csb_resp_src_valid ##3
    cacc2csb_resp_dst_valid ##1 !cacc2csb_resp_dst_valid [*2] ##1 cacc2csb_resp_dst_valid
  );

endmodule

bind NV_NVDLA_RT_csb2cacc NV_NVDLA_RT_csb2cacc_sva sva (
  .nvdla_core_clk               (nvdla_core_clk),
  .nvdla_core_rstn              (nvdla_core_rstn),

  .csb2cacc_req_src_pvld        (csb2cacc_req_src_pvld),
  .csb2cacc_req_src_prdy        (csb2cacc_req_src_prdy),
  .csb2cacc_req_src_pd          (csb2cacc_req_src_pd),

  .cacc2csb_resp_src_valid      (cacc2csb_resp_src_valid),
  .cacc2csb_resp_src_pd         (cacc2csb_resp_src_pd),

  .csb2cacc_req_dst_pvld        (csb2cacc_req_dst_pvld),
  .csb2cacc_req_dst_pd          (csb2cacc_req_dst_pd),
  .csb2cacc_req_dst_prdy        (csb2cacc_req_dst_prdy),

  .cacc2csb_resp_dst_valid      (cacc2csb_resp_dst_valid),
  .cacc2csb_resp_dst_pd         (cacc2csb_resp_dst_pd),

  .csb2cacc_req_pvld_d1         (csb2cacc_req_pvld_d1),
  .csb2cacc_req_pvld_d2         (csb2cacc_req_pvld_d2),
  .csb2cacc_req_pvld_d3         (csb2cacc_req_pvld_d3),
  .csb2cacc_req_pd_d1           (csb2cacc_req_pd_d1),
  .csb2cacc_req_pd_d2           (csb2cacc_req_pd_d2),
  .csb2cacc_req_pd_d3           (csb2cacc_req_pd_d3),

  .cacc2csb_resp_valid_d1       (cacc2csb_resp_valid_d1),
  .cacc2csb_resp_valid_d2       (cacc2csb_resp_valid_d2),
  .cacc2csb_resp_valid_d3       (cacc2csb_resp_valid_d3),
  .cacc2csb_resp_pd_d1          (cacc2csb_resp_pd_d1),
  .cacc2csb_resp_pd_d2          (cacc2csb_resp_pd_d2),
  .cacc2csb_resp_pd_d3          (cacc2csb_resp_pd_d3)
);