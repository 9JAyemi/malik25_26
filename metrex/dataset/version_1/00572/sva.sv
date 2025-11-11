// SystemVerilog Assertions for up_axi
// Bind into the DUT or include under ASSERT_ON
// Focused, high-quality checks with essential coverage

`ifndef UP_AXI_SVA
`define UP_AXI_SVA

bind up_axi up_axi_sva();

module up_axi_sva;

  default clocking cb @(posedge up_clk); endclocking
  default disable iff (!up_rstn);

  // Sanity/constancy
  assert property (up_axi_bresp == 2'd0);
  assert property (up_axi_rresp == 2'd0);
  assert property (!$isunknown({up_axi_awready,up_axi_wready,up_axi_bvalid,
                                up_axi_arready,up_axi_rvalid,up_axi_rdata,
                                up_wreq,up_waddr,up_wdata,up_rreq,up_raddr})));

  // Ready pulses are single-cycle and aligned
  assert property (up_axi_awready |=> !up_axi_awready);
  assert property (up_axi_wready  |=> !up_axi_wready);
  assert property (up_axi_arready |=> !up_axi_arready);
  assert property (up_axi_awready == up_axi_wready);
  // Ready only when a transaction is outstanding
  assert property (up_axi_awready |-> up_wsel);
  assert property (up_axi_wready  |-> up_wsel);
  assert property (up_axi_arready |-> up_rsel);

  // BVALID/RVALID hold under backpressure and clear on handshake
  assert property ((up_axi_bvalid && !up_axi_bready) |=> up_axi_bvalid);
  assert property ((up_axi_bvalid &&  up_axi_bready) |=> !up_axi_bvalid);
  assert property ((up_axi_rvalid && !up_axi_rready) |=> up_axi_rvalid);
  assert property ((up_axi_rvalid &&  up_axi_rready) |=> !up_axi_rvalid);

  // BVALID asserted with AWREADY/WREADY pulse
  assert property (up_axi_awready |-> up_axi_bvalid);
  assert property (up_axi_wready  |-> up_axi_bvalid);

  // Liveness (bounded) guarantees
  // Write request must produce AWREADY&WREADY&BVALID within 9 cycles (timeout guarantees progress)
  assert property (up_wreq |-> ##[1:9] (up_axi_awready && up_axi_wready && up_axi_bvalid));
  // Read request must produce ARREADY within 9 cycles and RVALID within 10 cycles (timeout guarantees progress)
  assert property (up_rreq |-> ##[1:9]  up_axi_arready);
  assert property (up_rreq |-> ##[1:10] up_axi_rvalid);

  // Address/data capture and stability
  assert property (up_wreq |-> (up_waddr == up_axi_awaddr[AW+2:2]) && (up_wdata == up_axi_wdata));
  assert property (up_wsel |-> $stable({up_waddr,up_wdata}) && !up_wreq);
  assert property (up_rreq |-> (up_raddr == up_axi_araddr[AW+2:2]));
  assert property (up_rsel |-> $stable(up_raddr) && !up_rreq);

  // No new req while a transaction is outstanding
  assert property (up_wsel |-> !(up_axi_awvalid && up_axi_wvalid));
  assert property (up_rsel |-> !up_axi_arvalid);

  // Clear select flags on response handshake
  assert property (up_wsel && up_axi_bvalid && up_axi_bready |=> !up_wsel);
  assert property (up_rsel && up_axi_rvalid && up_axi_rready |=> !up_rsel);

  // Timeout semantics (write): if wack not received by count==7, pulse readies and set bvalid 2 cycles later
  assert property (up_wsel && (up_wcount == 3'h7) && !up_wack |-> ##2 (up_axi_awready && up_axi_wready && up_axi_bvalid));

  // Timeout semantics (read): if rack not received by count==15, ARREADY in 2 cycles, RVALID in 3 cycles
  assert property ((up_rcount == 4'hf) && !up_rack |-> ##2 up_axi_arready ##1 up_axi_rvalid);

  // RDATA correctness
  // On any RVALID rise, RDATA equals the registered internal data used to drive it
  assert property ($rose(up_axi_rvalid) |-> (up_axi_rdata == up_rdata_int_d));
  // On timeout, delivered RDATA is 32'hDEAD_DEAD
  assert property ((up_rcount == 4'hf) && !up_rack |-> ##3 (up_axi_rvalid && (up_axi_rdata == 32'hDEAD_DEAD)));
  // While holding RVALID without RREADY, RDATA is stable
  assert property (up_axi_rvalid && !up_axi_rready |=> $stable(up_axi_rdata));

  // AW/W ready-bvalid pulse ordering coverage
  cover property (up_wreq ##[1:9] up_axi_awready && up_axi_wready && up_axi_bvalid);
  // Read normal path coverage (with external ack)
  cover property (up_rreq ##[1:6] up_rack ##2 up_axi_arready ##1 up_axi_rvalid);
  // Read timeout coverage
  cover property (up_rreq ##[7:12] up_axi_arready ##1 up_axi_rvalid && (up_axi_rdata == 32'hDEAD_DEAD));
  // Write timeout coverage
  cover property (up_wreq ##[7:12] up_axi_awready && up_axi_wready && up_axi_bvalid && !up_wack);

endmodule

`endif // UP_AXI_SVA