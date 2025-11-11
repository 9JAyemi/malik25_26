// SVA checker for memory_block_generator
module memory_block_generator_sva (memory_block_generator dut);

  // Local params inferred from DUT
  localparam int DATA_W = 3;
  localparam int ADDR_W = 13;
  localparam int DEPTH  = 8192;

  // Word index used by DUT (note: DUT uses addra[12:1])
  wire [ADDR_W-2:0] word_idx = dut.addra[12:1];

  // Simple reference model for functional checking
  logic [DATA_W-1:0] ref_mem [0:DEPTH-1];
  bit                wrote   [0:DEPTH-1];

  default clocking cb @(posedge dut.clka); endclocking

  // Combinational write-through check (bypass when wea=1)
  always_comb begin
    assert (!(dut.wea[0]) || (dut.douta == dut.dina))
      else $error("Bypass failure: wea=1 but douta!=dina");
  end

  // Basic input/output knownness
  a_no_x_inputs: assert property ( !$isunknown({dut.wea, dut.addra, dut.dina}) )
    else $error("Inputs contain X/Z");
  a_no_x_dout:   assert property ( !$isunknown(dut.douta) )
    else $error("douta contains X/Z");

  // Reference model updates on write
  always_ff @(posedge dut.clka) begin
    if (dut.wea[0]) begin
      ref_mem[word_idx] <= dut.dina;
      wrote[word_idx]   <= 1'b1;
    end
  end

  // Read must match model when not writing and address has been written before
  a_read_ok: assert property ( (!dut.wea[0] && wrote[word_idx]) |-> (dut.douta == ref_mem[word_idx]) )
    else $error("Read data mismatch");

  // Write then next-cycle read-back on same address (with write deasserted)
  a_wr_then_rd_same: assert property (
      dut.wea[0]
      ##1 (!dut.wea[0] && $stable(dut.addra)) |-> (dut.douta == $past(dut.dina))
    ) else $error("Write->readback mismatch on same address");

  // Stable read when idle and address stable
  a_stable_read: assert property ( (!dut.wea[0] && $stable(dut.addra)) |=> $stable(dut.douta) )
    else $error("douta changed while idle and address stable");

  // Coverage
  c_write:             cover property ( dut.wea[0] );
  c_read:              cover property ( !dut.wea[0] );
  c_wr_rd:             cover property ( dut.wea[0] ##1 (!dut.wea[0] && $stable(dut.addra)) );
  c_addr_first_write:  cover property ( dut.wea[0] && (dut.addra == 13'h0000) );
  c_addr_last_write:   cover property ( dut.wea[0] && (dut.addra == 13'h1FFF) );
  c_lsb0_read:         cover property ( !dut.wea[0] && (dut.addra[0] == 1'b0) );
  c_lsb1_read:         cover property ( !dut.wea[0] && (dut.addra[0] == 1'b1) );

endmodule

// Bind into DUT
bind memory_block_generator memory_block_generator_sva u_memory_block_generator_sva(.dut(this));