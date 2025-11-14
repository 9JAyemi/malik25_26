// SVA for soc_system_button_pio
`ifndef SOC_SYSTEM_BUTTON_PIO_SVA
`define SOC_SYSTEM_BUTTON_PIO_SVA

module soc_system_button_pio_sva_bind();
  default clocking cb @(posedge clk); endclocking
  default disable iff (!reset_n)

  // Invariants and simple relations
  assert property (clk_en);
  assert property (data_in == in_port);
  assert property (irq == |(edge_capture & irq_mask));

  // Reset values (checked while reset is asserted)
  assert property (@(posedge clk) !reset_n |-> (readdata==32'd0 && irq_mask==2'd0 && edge_capture==2'd0 && d1_data_in==2'd0 && d2_data_in==2'd0));

  // Read data mapping and zero-extend (registered one cycle after mux eval)
  assert property ($past(reset_n) |-> (readdata[31:2] == 30'd0));
  assert property ($past(reset_n) |-> (readdata[1:0] ==
                    $past((({2{address==2'd0}} & data_in) |
                           ({2{address==2'd2}} & irq_mask) |
                           ({2{address==2'd3}} & edge_capture)))) );
  assert property ((address==2'd1) |=> (readdata[1:0]==2'd0));

  // irq_mask write protocol
  assert property ((chipselect && !write_n && address==2'd2) |=> (irq_mask == $past(writedata[1:0])));
  assert property (!(chipselect && !write_n && address==2'd2) |=> $stable(irq_mask));

  // 2-stage sync and edge detect (guard for 2-cycle history)
  assert property ($past(reset_n,2) |-> (d1_data_in == $past(data_in)));
  assert property ($past(reset_n,2) |-> (d2_data_in == $past(d1_data_in)));
  assert property ($past(reset_n,2) |-> (edge_detect == (~$past(data_in,1) & $past(data_in,2))));

  // Edge capture behavior (clear has priority over set)
  genvar i;
  generate for (i=0;i<2;i++) begin : g_cap
    // Clear on write '1' to address 3
    assert property ((edge_capture_wr_strobe && writedata[i]) |=> (edge_capture[i]==1'b0));
    // Set on detected falling edge if not being cleared
    assert property ((edge_detect[i] && !(edge_capture_wr_strobe && writedata[i]))
                     |=> (edge_capture[i] == ~$past(in_port[i])));
    // Hold otherwise
    assert property ((!(edge_capture_wr_strobe && writedata[i]) && !edge_detect[i]) |=> $stable(edge_capture[i]));
    // Cover precedence when clear and detect coincide
    cover property ((edge_capture_wr_strobe && writedata[i] && edge_detect[i]) ##1 (edge_capture[i]==1'b0));
  end endgenerate

  // Address decode coverage
  cover property (address==2'd0);
  cover property (address==2'd2);
  cover property (address==2'd3);

  // End-to-end covers for each bit: mask -> fall -> irq -> clear -> no irq
  sequence wr_mask0; chipselect && !write_n && address==2'd2 && writedata[0]; endsequence
  sequence clr_cap0; chipselect && !write_n && address==2'd3 && writedata[0]; endsequence
  cover property (wr_mask0 ##1 $fell(in_port[0]) ##1 irq ##1 clr_cap0 ##1 !irq);

  sequence wr_mask1; chipselect && !write_n && address==2'd2 && writedata[1]; endsequence
  sequence clr_cap1; chipselect && !write_n && address==2'd3 && writedata[1]; endsequence
  cover property (wr_mask1 ##1 $fell(in_port[1]) ##1 irq ##1 clr_cap1 ##1 !irq);
endmodule

bind soc_system_button_pio soc_system_button_pio_sva_bind;

`endif