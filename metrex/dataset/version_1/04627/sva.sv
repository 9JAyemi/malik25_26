// Bindable SVA for dual_port_RAM
// Place inside the module or bind as: bind dual_port_RAM dual_port_RAM_sva sva();

module dual_port_RAM_sva;
  // Access DUT scope directly when bound into dual_port_RAM
  // clk, rst_n, write_en, write_addr, write_data, read_en, read_addr, read_data,
  // write_port, read_port, read_data_t, ram are visible here

  // Reset behavior (active-low async): regs/output forced to 0 while reset low
  ap_reset_zero: assert property (@(posedge clk) !rst_n |-> (write_port==3'b0 && read_port==3'b0 && read_data==4'h0));

  // Write-port latching from address LSBs
  ap_wr_port_latch: assert property (@(posedge clk) disable iff (!rst_n)
                                     write_en |=> (write_port == $past(write_addr[2:0])));
  // Write-port holds when not writing
  ap_wr_hold:       assert property (@(posedge clk) disable iff (!rst_n)
                                     !write_en |=> (write_port == $past(write_port)));

  // RAM update occurs at previous write_port index; other cycles no change
  property p_write_effect;
    logic [2:0] idx; logic [3:0] val;
    @(posedge clk) disable iff (!rst_n)
      (write_en, idx = write_port, val = write_data) |=> (ram[idx] == val);
  endproperty
  ap_write_effect: assert property (p_write_effect);

  genvar gi;
  generate
    for (gi=0; gi<8; gi++) begin : G_RAM_STABLE_NO_WRITE
      ap_ram_stable_no_write: assert property (@(posedge clk) disable iff (!rst_n)
                                              !write_en |=> (ram[gi] == $past(ram[gi])));
    end
  endgenerate

  // Read-port latching from address LSBs
  ap_rd_port_latch: assert property (@(posedge clk) disable iff (!rst_n)
                                     read_en |=> (read_port == $past(read_addr[2:0])));
  // Read-data and read_port hold when not reading
  ap_rd_hold:       assert property (@(posedge clk) disable iff (!rst_n)
                                     !read_en |=> (read_port == $past(read_port) && read_data == $past(read_data)));

  // Read latency/correctness: data reflects snapshot of RAM at previous read_port
  property p_read_latency;
    logic [2:0] idx; logic [3:0] val;
    @(posedge clk) disable iff (!rst_n)
      (read_en, idx = read_port, val = ram[idx]) |=> (read_data == val);
  endproperty
  ap_read_latency: assert property (p_read_latency);

  // Output wire matches internal register
  ap_rd_wire_consistent: assert property (@(posedge clk) (read_data == read_data_t));

  // Coverage
  genvar gc;
  generate
    for (gc=0; gc<8; gc++) begin : G_COV_ADDRS
      cp_wr_each_addr: cover property (@(posedge clk) write_en && write_addr[2:0] == gc[2:0]);
      cp_rd_each_addr: cover property (@(posedge clk) read_en  && read_addr[2:0]  == gc[2:0]);
    end
  endgenerate
  cp_rw_same_prev_port: cover property (@(posedge clk) read_en && write_en && (read_port == write_port));
  cp_wr_highbits:       cover property (@(posedge clk) write_en && (write_addr[7:3] != 5'b0));
  cp_rd_highbits:       cover property (@(posedge clk) read_en  && (read_addr[7:3]  != 5'b0));
endmodule

// Example bind
// bind dual_port_RAM dual_port_RAM_sva sva();