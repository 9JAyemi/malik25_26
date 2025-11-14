// SVA for top_module
// Bind into DUT to access internal regs/mem
module top_module_sva;

  // Default clock
  default clocking cb @(posedge clk); endclocking

  // Simple mirror of 8x4 RAM to check read datapath semantically
  logic [3:0] mem_mirror [0:7];
  logic       mem_valid  [0:7];
  integer i;

  // Mirror update
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      for (i=0;i<8;i++) begin
        mem_mirror[i] <= '0;
        mem_valid[i]  <= 1'b0;
      end
    end
    else begin
      if (write_en && (write_addr < 8)) begin
        mem_mirror[write_addr[2:0]] <= write_data;
        mem_valid[write_addr[2:0]]  <= 1'b1;
      end
    end
  end

  // -------------------------
  // Reset behavior
  // -------------------------
  ap_reset_ptrs: assert property (!rst_n |-> (write_ptr==0 && read_ptr==0));

  // -------------------------
  // Pointer update behavior
  // -------------------------
  ap_wr_ptr_inc:  assert property (disable iff (!rst_n) write_en  |=> write_ptr == $past(write_ptr) + 1);
  ap_wr_ptr_hold: assert property (disable iff (!rst_n) !write_en |=> write_ptr == $past(write_ptr));

  ap_rd_ptr_inc:  assert property (disable iff (!rst_n) read_en  |=> read_ptr == $past(read_ptr) + 1);
  ap_rd_ptr_hold: assert property (disable iff (!rst_n) !read_en |=> read_ptr == $past(read_ptr));

  // read_ptr is used to index 8-deep RAM each cycle; must remain in-range
  ap_rdptr_in_range: assert property (disable iff (!rst_n) read_ptr < 8);

  // -------------------------
  // Address range on external accesses
  // -------------------------
  ap_wr_addr_range: assert property (disable iff (!rst_n) write_en |-> (write_addr < 8));
  ap_rd_addr_range: assert property (disable iff (!rst_n) read_en  |-> (read_addr  < 8));

  // -------------------------
  // Mux behavior
  // -------------------------
  function automatic [3:0] mux_default_and;
    mux_default_and = (data0 & 4'h3) & (data1 & 4'h3) & (data2 & 4'h3) &
                      (data3 & 4'h3) & (data4 & 4'h3) & (data5 & 4'h3);
  endfunction

  ap_mux_000: assert property (disable iff (!rst_n) (sel==3'b000) |=> mux_out == $past(data0));
  ap_mux_001: assert property (disable iff (!rst_n) (sel==3'b001) |=> mux_out == $past(data1));
  ap_mux_010: assert property (disable iff (!rst_n) (sel==3'b010) |=> mux_out == $past(data2));
  ap_mux_011: assert property (disable iff (!rst_n) (sel==3'b011) |=> mux_out == $past(data3));
  ap_mux_100: assert property (disable iff (!rst_n) (sel==3'b100) |=> mux_out == $past(data4));
  ap_mux_101: assert property (disable iff (!rst_n) (sel==3'b101) |=> mux_out == $past(data5));
  ap_mux_def: assert property (disable iff (!rst_n) (sel inside {3'b110,3'b111}) |=> mux_out == $past(mux_default_and()));

  // -------------------------
  // RAM read datapath checks using mirror
  // -------------------------
  // ram_out1 updates only when read_en; value is RAM content as of previous cycle at read_addr
  ap_ram_out1_hold: assert property (disable iff (!rst_n) !read_en |=> ram_out1 == $past(ram_out1));

  ap_ram_out1_val: assert property (disable iff (!rst_n)
    read_en |=> ( !$past(mem_valid[$past(read_addr[2:0])])
                  or (ram_out1 == $past(mem_mirror[$past(read_addr[2:0])])) )
  );

  // ram_out2 updates every cycle with RAM content (previous cycle) at read_ptr
  ap_ram_out2_val: assert property (disable iff (!rst_n)
    1'b1 |=> ( !$past(mem_valid[$past(read_ptr[2:0])])
               or (ram_out2 == $past(mem_mirror[$past(read_ptr[2:0])])) )
  );

  // Same-cycle write/read to same address returns old data on ram_out1
  ap_rw_same_addr_olddata: assert property (disable iff (!rst_n)
    (write_en && read_en && (write_addr[2:0]==read_addr[2:0])) |=> ram_out1 == $past(mem_mirror[$past(read_addr[2:0])])
  );

  // -------------------------
  // Final output relation
  // -------------------------
  ap_final_or: assert property (disable iff (!rst_n) 1'b1 |=> final_output == $past(ram_out1 | ram_out2 | mux_out));

  // -------------------------
  // X/Z checks after reset
  // -------------------------
  ap_nox_final: assert property (disable iff (!rst_n) !$isunknown(final_output));
  ap_nox_mux:   assert property (disable iff (!rst_n) !$isunknown(mux_out));
  ap_nox_ro1:   assert property (disable iff (!rst_n) !$isunknown(ram_out1));
  ap_nox_ro2:   assert property (disable iff (!rst_n) !$isunknown(ram_out2));

  // -------------------------
  // Coverage
  // -------------------------
  cv_reset_then_ops: cover property (disable iff (!rst_n)
    $rose(rst_n) ##1 write_en ##1 read_en);

  cv_mux_each_sel: cover property (disable iff (!rst_n)
    sel==3'b000 ##1 sel==3'b001 ##1 sel==3'b010 ##1 sel==3'b011 ##1 sel==3'b100 ##1 sel==3'b101 ##1 sel inside {3'b110,3'b111});

  cv_rw_same_addr: cover property (disable iff (!rst_n)
    write_en && read_en && (write_addr[2:0]==read_addr[2:0]));

  cv_final_uses_all: cover property (disable iff (!rst_n)
    (ram_out1!=0 && ram_out2!=0 && mux_out!=0) ##1 (final_output == $past(ram_out1 | ram_out2 | mux_out)));

endmodule

bind top_module top_module_sva();