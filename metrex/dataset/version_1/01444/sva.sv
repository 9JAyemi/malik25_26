// Bind these SVA to the DUT
bind i2c_control i2c_control_sva i2c_control_sva_inst();

module i2c_control_sva;
  // These assertions are bound inside i2c_control and can see its names directly.
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Basic equivalences and combinational mappings
  a_memw_eq:       assert property (memw == (write && (address>=3'd1) && (address<=3'd5)));
  a_i2c_data:      assert property (i2c_data == {writedata[7:4], !writedata[4], writedata[3:0], !writedata[0]});

  // memd decode
  a_memd_2:        assert property ((address==3'd2) |-> (memd == {2'b00, i2c_data}));
  a_memd_3:        assert property ((address==3'd3) |-> (memd == {2'b10, i2c_data}));
  a_memd_4:        assert property ((address==3'd4) |-> (memd == {2'b01, i2c_data}));
  a_memd_5:        assert property ((address==3'd5) |-> (memd == {2'b11, i2c_data}));
  a_memd_def:      assert property ((!(address inside {3'd2,3'd3,3'd4,3'd5})) |-> (memd == writedata[11:0]));

  // readdata muxing
  a_rdata_1:       assert property ((address==3'd1) |-> (readdata == rda));
  a_rdata_def:     assert property ((address!=3'd1) |-> (readdata == {28'h1234_567, 1'b0, full, rdbff, (busy || rda[31])}));

  // go/rdbff sequential behavior (next-cycle check due to flop update semantics)
  a_go_next:       assert property (1'b1 |=> (go == ($past(write && (address==3'd0)) ? $past(writedata[0]) : 1'b0)));
  a_rdbff_next:    assert property (1'b1 |=> (rdbff == ($past(write && (address==3'd0)) ? $past(writedata[1]) : $past(rdbff))));

  // tbm mirrors rdbff
  a_tbm_eq:        assert property (tbm == rdbff);

  // Asynchronous reset effect visible at clock edge
  a_async_reset:   assert property (disable iff(1'b0) @(posedge clk) reset |-> (go==1'b0 && rdbff==1'b0));

  // Known-value checks after reset deasserted
  a_known_outs:    assert property (!$isunknown({go, tbm, memw, memd, readdata})));

  // ----------------------------------
  // Coverage (key use-cases/features)
  // ----------------------------------
  // Addressed writes drive memw
  c_memw_1:        cover property (write && address==3'd1 && memw);
  c_memw_2:        cover property (write && address==3'd2 && memw);
  c_memw_3:        cover property (write && address==3'd3 && memw);
  c_memw_4:        cover property (write && address==3'd4 && memw);
  c_memw_5:        cover property (write && address==3'd5 && memw);

  // Control register writes (address 0)
  c_go_pulse:      cover property (write && address==3'd0 && writedata[0]);
  c_rdbff_set:     cover property (write && address==3'd0 && writedata[1]);
  c_rdbff_clr:     cover property (write && address==3'd0 && !writedata[1]);
  c_rdbff_toggle:  cover property ((write && address==3'd0 && writedata[1]) ##1 (write && address==3'd0 && !writedata[1]));

  // Read paths
  c_read_addr1:    cover property (read && address==3'd1);
  c_read_other:    cover property (read && address!=3'd1);

  // Default readdata LSB behavior
  c_rdata_lsb1:    cover property ((address!=3'd1) && (busy || rda[31]) && readdata[0]);
  c_rdata_lsb0:    cover property ((address!=3'd1) && !busy && !rda[31] && !readdata[0]);

  // Exercise i2c_data inversion bits
  c_i2c_inv4_0:    cover property (writedata[4]==1'b0);
  c_i2c_inv4_1:    cover property (writedata[4]==1'b1);
  c_i2c_inv0_0:    cover property (writedata[0]==1'b0);
  c_i2c_inv0_1:    cover property (writedata[0]==1'b1);

  // memd prefixes for addr 2..5
  c_memd_pref_2:   cover property (address==3'd2 && memd[11:10]==2'b00);
  c_memd_pref_3:   cover property (address==3'd3 && memd[11:10]==2'b10);
  c_memd_pref_4:   cover property (address==3'd4 && memd[11:10]==2'b01);
  c_memd_pref_5:   cover property (address==3'd5 && memd[11:10]==2'b11);
endmodule