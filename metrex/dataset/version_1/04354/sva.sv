// SVA bind module for axi_slave_impl
// Focus: AXI4-Lite protocol, data-path correctness, register_operation side-channel,
// coverage of key scenarios. Concise, high-signal-to-noise.

module axi_slave_impl_sva #(
  parameter int NUMBER_OF_REGISTERS = 16,
  parameter int C_S_AXI_DATA_WIDTH  = 32,
  parameter int C_S_AXI_ADDR_WIDTH  = 10
) ();

  // local constants
  localparam int BYTES            = C_S_AXI_DATA_WIDTH/8;
  localparam int ADDR_LSB_SVA     = (C_S_AXI_DATA_WIDTH/32) + 1;
  localparam int OPT_MEM_ADDRBITS = C_S_AXI_ADDR_WIDTH - ADDR_LSB_SVA - 1;

  // mirror of macro values
  localparam int REGISTER_READ_OPERATION  = 1;
  localparam int REGISTER_WRITE_OPERATION = 2;

  // default clocking and reset
  default clocking cb @(posedge S_AXI_ACLK); endclocking
  default disable iff (!S_AXI_ARESETN);

  // handy lets
  let aw_index = axi_awaddr[ADDR_LSB_SVA+OPT_MEM_ADDRBITS : ADDR_LSB_SVA];
  let ar_index = axi_araddr[ADDR_LSB_SVA+OPT_MEM_ADDRBITS : ADDR_LSB_SVA];

  // Reset values
  assert property (!S_AXI_ARESETN |-> !S_AXI_AWREADY && !S_AXI_WREADY && !S_AXI_BVALID
                                && !S_AXI_ARREADY && !S_AXI_RVALID
                                && S_AXI_BRESP==2'b00 && S_AXI_RRESP==2'b00);
  genvar r;
  generate
    for (r=0; r<NUMBER_OF_REGISTERS; r++) begin : g_rst_regs
      assert property (!S_AXI_ARESETN |-> registers[r]=='0);
    end
  endgenerate

  // AXI input stability until handshake
  assert property (S_AXI_AWVALID && !S_AXI_AWREADY |-> $stable(S_AXI_AWADDR) && $stable(S_AXI_AWPROT));
  assert property (S_AXI_WVALID  && !S_AXI_WREADY  |-> $stable(S_AXI_WDATA) && $stable(S_AXI_WSTRB));
  assert property (S_AXI_ARVALID && !S_AXI_ARREADY |-> $stable(S_AXI_ARADDR) && $stable(S_AXI_ARPROT));

  // AW/W ready behavior and write accept
  assert property (S_AXI_AWREADY |-> S_AXI_AWVALID && S_AXI_WVALID);
  assert property (S_AXI_WREADY  |-> S_AXI_WVALID  && S_AXI_AWVALID);
  assert property ($rose(S_AXI_AWREADY) |-> ##1 !S_AXI_AWREADY);
  assert property ($rose(S_AXI_WREADY)  |-> ##1 !S_AXI_WREADY);
  assert property (S_AXI_AWREADY == S_AXI_WREADY);

  // slv_reg_wren definition and bounds
  assert property (slv_reg_wren == (S_AXI_WVALID && S_AXI_AWVALID && S_AXI_WREADY && S_AXI_AWREADY));
  assert property (slv_reg_wren |-> aw_index < NUMBER_OF_REGISTERS);

  // Byte-lane masked write correctness (next cycle)
  genvar b;
  generate
    for (b=0; b<BYTES; b++) begin : g_wmask_chk
      assert property ($past(slv_reg_wren) && $past(S_AXI_WSTRB[b])
                       |-> registers[$past(aw_index)][(b*8)+:8] == $past(S_AXI_WDATA[(b*8)+:8]));
      assert property ($past(slv_reg_wren) && !$past(S_AXI_WSTRB[b])
                       |-> registers[$past(aw_index)][(b*8)+:8] == $past(registers[$past(aw_index)][(b*8)+:8]));
    end
  endgenerate

  // Write response channel
  assert property ($rose(slv_reg_wren) |=> S_AXI_BVALID);
  assert property (S_AXI_BVALID |-> S_AXI_BRESP==2'b00);
  assert property (S_AXI_BVALID && !S_AXI_BREADY |-> S_AXI_BVALID && $stable(S_AXI_BRESP));
  assert property ($rose(S_AXI_BVALID) |-> S_AXI_BVALID until_with S_AXI_BREADY);

  // AR/R ready/valid behavior
  assert property (S_AXI_ARREADY |-> S_AXI_ARVALID);
  assert property ($rose(S_AXI_ARREADY) |-> ##1 !S_AXI_ARREADY);
  assert property (slv_reg_rden == (S_AXI_ARREADY && S_AXI_ARVALID && !S_AXI_RVALID));
  assert property ($rose(slv_reg_rden) |=> S_AXI_RVALID);
  assert property (S_AXI_RVALID |-> S_AXI_RRESP==2'b00);
  assert property (S_AXI_RVALID && !S_AXI_RREADY |-> S_AXI_RVALID && $stable(S_AXI_RDATA) && $stable(S_AXI_RRESP));
  // Read data correctness (next cycle after accept)
  assert property (slv_reg_rden |=> (($past(ar_index) < NUMBER_OF_REGISTERS)
                                      ? (S_AXI_RDATA == $past(registers[$past(ar_index)]))
                                      : (S_AXI_RDATA == '0)));

  // Side-channel register_operation constraints and effects
  assert property (!slv_reg_wren && register_operation==REGISTER_WRITE_OPERATION
                   |-> register_number>0 && register_number<=NUMBER_OF_REGISTERS);
  assert property (!slv_reg_rden && register_operation==REGISTER_READ_OPERATION
                   |-> register_number>0 && register_number<=NUMBER_OF_REGISTERS);
  assert property (!slv_reg_wren && register_operation==REGISTER_WRITE_OPERATION
                   && register_number>0 && register_number<=NUMBER_OF_REGISTERS
                   |=> registers[$past(register_number)-1] == $past(register_write));
  assert property (!slv_reg_rden && register_operation==REGISTER_READ_OPERATION
                   && register_number>0 && register_number<=NUMBER_OF_REGISTERS
                   |=> register_read == $past(registers[$past(register_number)-1]));

  // Basic X-check after reset release
  assert property ($rose(S_AXI_ARESETN) |-> ##1 !$isunknown({S_AXI_AWREADY,S_AXI_WREADY,S_AXI_BVALID,
                                                             S_AXI_ARREADY,S_AXI_RVALID,S_AXI_BRESP,S_AXI_RRESP}));

  // Coverage
  cover property (S_AXI_AWVALID && S_AXI_WVALID && S_AXI_AWREADY && S_AXI_WREADY);
  cover property (S_AXI_BVALID && S_AXI_BREADY);
  cover property (S_AXI_ARVALID && S_AXI_ARREADY);
  cover property (S_AXI_RVALID && S_AXI_RREADY);
  cover property (slv_reg_wren && (S_AXI_WSTRB != '0) && (S_AXI_WSTRB != {BYTES{1'b1}}));
  cover property (register_operation==REGISTER_WRITE_OPERATION);
  cover property (register_operation==REGISTER_READ_OPERATION);
  cover property (slv_reg_rden && ($past(ar_index) >= NUMBER_OF_REGISTERS));

endmodule

bind axi_slave_impl axi_slave_impl_sva #(
  .NUMBER_OF_REGISTERS(NUMBER_OF_REGISTERS),
  .C_S_AXI_DATA_WIDTH (C_S_AXI_DATA_WIDTH),
  .C_S_AXI_ADDR_WIDTH (C_S_AXI_ADDR_WIDTH)
) ();