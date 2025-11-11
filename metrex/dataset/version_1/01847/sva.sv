// SVA for blockmem2r1wptr
// Bind into the DUT; uses hierarchical refs to internal regs/arrays.
module blockmem2r1wptr_sva ();
  default clocking cb @(posedge clk); endclocking

  // Asynchronous reset behavior
  a_async_immediate: assert property (@(negedge reset_n) ##0 (ptr_reg == 8'h00));
  a_async_hold:      assert property (@(posedge clk) !reset_n |-> (ptr_reg == 8'h00));

  // Pointer behavior (disable during async reset)
  a_ptr_inc:        assert property (disable iff (!reset_n) cs               |=> ptr_reg == $past(ptr_reg) + 8'h01);
  a_ptr_rst_only:   assert property (disable iff (!reset_n) rst && !cs       |=> ptr_reg == 8'h00);
  a_ptr_hold:       assert property (disable iff (!reset_n) !rst && !cs      |=> ptr_reg == $past(ptr_reg));
  a_ptr_wrap:       assert property (disable iff (!reset_n) $past(ptr_reg)==8'hFF && cs |=> ptr_reg == 8'h00);
  a_cs_priority:    assert property (disable iff (!reset_n) rst && cs        |=> ptr_reg == $past(ptr_reg) + 8'h01);

  // Output wiring
  a_rd0_wired: assert property (read_data0 === tmp_read_data0);
  a_rd1_wired: assert property (read_data1 === tmp_read_data1);

  // Read pipelines model mem access timing
  property p_r0;
    logic [7:0] a;
    (1'b1, a = read_addr0) |-> (tmp_read_data0 == $past(mem[a]));
  endproperty
  a_r0: assert property (disable iff (!reset_n) p_r0);

  property p_r1;
    logic [7:0] p;
    (1'b1, p = ptr_reg) |-> (tmp_read_data1 == $past(mem[p]));
  endproperty
  a_r1: assert property (disable iff (!reset_n) p_r1);

  // Write updates memory at old ptr address (visible next cycle in mem)
  a_mem_write: assert property (disable iff (!reset_n) wr |=> mem[$past(ptr_reg)] == $past(write_data));

  // Visibility scenarios
  // If ptr doesn't move for 2 cycles after a write, rd1 shows data in 2 cycles
  a_wr_vis_rd1: assert property (disable iff (!reset_n)
                                 (wr && !cs) ##1 (!cs) |=> read_data1 == $past(write_data,2));
  // If rd0 targets the write address at N+1, rd0 shows data in 2 cycles
  property p_wr_vis_rd0;
    logic [7:0] a;
    (wr, a = ptr_reg) ##1 (read_addr0 == a) |=> read_data0 == $past(write_data,2);
  endproperty
  a_wr_vis_rd0: assert property (disable iff (!reset_n) p_wr_vis_rd0);

  // Functional coverage
  c_ptr_rst:   cover property (disable iff (!reset_n) rst && !cs);
  c_ptr_inc:   cover property (disable iff (!reset_n) cs && !rst);
  c_both:      cover property (disable iff (!reset_n) rst && cs);
  c_wrap:      cover property (disable iff (!reset_n) (ptr_reg==8'hFF && cs) ##1 (ptr_reg==8'h00));
  c_wr_rd1:    cover property (disable iff (!reset_n) (wr && !cs) ##1 !cs ##1 (read_data1 == $past(write_data,2)));
endmodule

bind blockmem2r1wptr blockmem2r1wptr_sva sva_inst();