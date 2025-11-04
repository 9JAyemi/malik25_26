/*
 * SVA QUALITY EVALUATION
 * ======================
 * The pipeline assertions have fundamental correctness issues. Property `p_req_pd_propagate` has
 * broken logic: the antecedent checks if `csb2cacc_req_src_pd == csb2cacc_req_dst_pd` at cycle 0,
 * but these are input and output of a 3-stage pipeline, so they should NOT be equal until after
 * propagation - this makes the antecedent almost never trigger. The consequent then checks if
 * dst_pd equals src_pd at cycle 3, but src_pd may have changed by then, so it should capture the
 * original value using `$past(csb2cacc_req_src_pd, 3)`. The prdy tie-high check is procedural and
 * should be a property. The reset assertion fires on both posedge and negedge, creating conflicting
 * evaluation contexts and potential race conditions with the actual reset logic. Critical gaps:
 * no verification of ready/valid handshaking protocol, no checks that data remains stable when
 * valid is asserted but not ready, no backpressure handling (prdy is forced high), and no overflow
 * protection if source produces data faster than pipeline can drain. The 3-cycle latency assumption
 * is hardcoded without verifying it matches actual DUT behavior.
 *
 * Most Significant Flaw: Property `p_req_pd_propagate` contains logically impossible antecedent
 * conditions (checking if pipeline input equals output before propagation occurs), making it
 * effectively non-functional for verification.
 *
 * Final Score: 4/10 - Basic pipeline latency checking exists but data propagation verification
 * is mathematically incorrect and handshaking protocol is not verified at all.
 */

/*
 * SECOND SVA QUALITY EVALUATION
 * =============================
 * The assertions contain severe logical and methodological flaws. The data propagation property, `p_req_pd_propagate`, is fundamentally broken; its antecedent `(csb2cacc_req_src_pd == csb2cacc_req_dst_pd)` requires the pipeline's input and output to be equal *before* propagation, making the check useless. Furthermore, the consequent compares the final output to the *current* input, not the original input from three cycles prior, failing to verify data integrity through the pipe. The reset check is a procedural assertion in a mixed-edge `always` block (`posedge clk or negedge rstn`), which is poor practice and can lead to simulation races.
 *
 * The verification is critically incomplete. It completely ignores the ready/valid handshaking protocol by simply asserting `csb2cacc_req_src_prdy` is tied high. This fails to check backpressure scenarios where `prdy` is low, a primary source of bugs in pipelined interfaces. There are no assertions to ensure that data remains stable when `pvld` is high but `prdy` is low, or that the pipeline correctly stalls and resumes. The fixed 3-cycle latency is assumed but not verified as a property of the DUT itself.
 *
 * Most Significant Flaw: The `p_req_pd_propagate` property is logically incorrect in both its trigger condition (antecedent) and its check (consequent), rendering it completely ineffective for verifying data propagation.
 *
 * Final Score: 3/10 - The assertions fail to correctly verify the core data-path and completely ignore the critical handshaking protocol, making them unsuitable for production verification.
 */

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
