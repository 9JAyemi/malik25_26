`timescale 1ns/1ps

module NV_NVDLA_RT_csb2cacc_sva();

  logic nvdla_core_clk;
  logic nvdla_core_rstn;

  logic csb2cacc_req_src_pvld;
  logic csb2cacc_req_src_prdy;
  logic [62:0] csb2cacc_req_src_pd;

  logic cacc2csb_resp_src_valid;
  logic [33:0] cacc2csb_resp_src_pd;

  logic csb2cacc_req_dst_pvld;
  logic csb2cacc_req_dst_prdy;
  logic [62:0] csb2cacc_req_dst_pd;

  logic cacc2csb_resp_dst_valid;
  logic [33:0] cacc2csb_resp_dst_pd;

  NV_NVDLA_RT_csb2cacc dut (
    .nvdla_core_clk(nvdla_core_clk),
    .nvdla_core_rstn(nvdla_core_rstn),
    .csb2cacc_req_src_pvld(csb2cacc_req_src_pvld),
    .csb2cacc_req_src_prdy(csb2cacc_req_src_prdy),
    .csb2cacc_req_src_pd(csb2cacc_req_src_pd),
    .cacc2csb_resp_src_valid(cacc2csb_resp_src_valid),
    .cacc2csb_resp_src_pd(cacc2csb_resp_src_pd),
    .csb2cacc_req_dst_pvld(csb2cacc_req_dst_pvld),
    .csb2cacc_req_dst_prdy(csb2cacc_req_dst_prdy),
    .csb2cacc_req_dst_pd(csb2cacc_req_dst_pd),
    .cacc2csb_resp_dst_valid(cacc2csb_resp_dst_valid),
    .cacc2csb_resp_dst_pd(cacc2csb_resp_dst_pd)
  );

  // simple clock
  initial nvdla_core_clk = 0;
  always #5 nvdla_core_clk = ~nvdla_core_clk;

  // prdy tie-high
  always @(posedge nvdla_core_clk) begin
    assert (csb2cacc_req_src_prdy == 1'b1) else $error("csb2cacc_req_src_prdy is not tied high");
  end

  // Pipeline valid propagation: source pvld appears at dst pvld after 3 cycles
  property p_req_pvld_propagate;
    @(posedge nvdla_core_clk) disable iff (!nvdla_core_rstn) csb2cacc_req_src_pvld |-> ##3 csb2cacc_req_dst_pvld;
  endproperty
  assert property (p_req_pvld_propagate) else $error("csb2cacc_req_src_pvld did not propagate to dst in 3 cycles");

  // Request data propagation: when pvld asserted, src_pd should equal dst_pd after 3 cycles
  property p_req_pd_propagate;
    @(posedge nvdla_core_clk) disable iff (!nvdla_core_rstn) (csb2cacc_req_src_pvld && (csb2cacc_req_src_pd == csb2cacc_req_dst_pd)) |-> ##3 (csb2cacc_req_dst_pd == csb2cacc_req_src_pd);
  endproperty
  assert property (p_req_pd_propagate) else $error("csb2cacc_req_pd did not propagate to dst in 3 cycles");

  // Response propagation
  property p_resp_propagate;
    @(posedge nvdla_core_clk) disable iff (!nvdla_core_rstn) cacc2csb_resp_src_valid |-> ##3 cacc2csb_resp_dst_valid;
  endproperty
  assert property (p_resp_propagate) else $error("cacc2csb_resp_src_valid did not propagate to dst in 3 cycles");

  // Reset clears pipeline valid regs
  always @(posedge nvdla_core_clk or negedge nvdla_core_rstn) begin
    if (!nvdla_core_rstn) begin
      assert (dut.csb2cacc_req_pvld_d1 == 1'b0 && dut.csb2cacc_req_pvld_d2 == 1'b0 && dut.csb2cacc_req_pvld_d3 == 1'b0 && dut.cacc2csb_resp_valid_d1 == 1'b0 && dut.cacc2csb_resp_valid_d2 == 1'b0 && dut.cacc2csb_resp_valid_d3 == 1'b0) else $error("Pipeline valid regs not cleared on reset");
    end
  end

  // small stimulus for simulation
  initial begin
    nvdla_core_rstn = 0;
    csb2cacc_req_src_pvld = 0; csb2cacc_req_src_pd = 63'd0; cacc2csb_resp_src_valid = 0; cacc2csb_resp_src_pd = 34'd0;
    #20;
    nvdla_core_rstn = 1;
    #20;
    csb2cacc_req_src_pd = 63'h1AA; csb2cacc_req_src_pvld = 1; #20; csb2cacc_req_src_pvld = 0;
    #100;
    cacc2csb_resp_src_pd = 34'h55; cacc2csb_resp_src_valid = 1; #20; cacc2csb_resp_src_valid = 0;
    #200;
    $finish;
  end

endmodule
