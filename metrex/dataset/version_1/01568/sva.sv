// SVA for mips_memory2
// Bind into the DUT for direct access to internals
module mips_memory2_sva #(parameter MEMSIZE = 1024, parameter START_ADDR = 32'h8002_0000) ();
  // Use DUT's clock and signals directly (bind inserts this in DUT scope)
  default clocking cb @(posedge clk); endclocking

  // Guard for $past usage
  bit past_valid;
  initial past_valid = 0;
  always @(posedge clk) past_valid <= 1'b1;
  default disable iff (!past_valid);

  // Invariants for interface wires
  a_busy_def:       assert property (busy == (reg_counter > 6'd1));
  a_output_def:     assert property (wire_output == (reg_counter != 6'd0));

  // reg_din samples din each cycle
  a_reg_din_sample: assert property (reg_din == $past(din));

  // reg_rw latch on new request, hold otherwise
  a_rw_latch:       assert property ((!wire_busy && enable) |-> ##0 (reg_rw == rw));
  a_rw_hold:        assert property ((wire_busy || !enable) |-> ##0 (reg_rw == $past(reg_rw)));

  // reg_counter load mapping on new request
  a_cnt_load_000:   assert property ((!wire_busy && enable && access_size==3'b000) |-> ##0 (reg_counter==6'd1));
  a_cnt_load_001:   assert property ((!wire_busy && enable && access_size==3'b001) |-> ##0 (reg_counter==6'd4));
  a_cnt_load_010:   assert property ((!wire_busy && enable && access_size==3'b010) |-> ##0 (reg_counter==6'd8));
  a_cnt_load_011:   assert property ((!wire_busy && enable && access_size==3'b011) |-> ##0 (reg_counter==6'd16));
  a_cnt_load_100:   assert property ((!wire_busy && enable && access_size==3'b100) |-> ##0 (reg_counter==6'd1));
  a_cnt_load_101:   assert property ((!wire_busy && enable && access_size==3'b101) |-> ##0 (reg_counter==6'd1));
  a_cnt_load_def0:  assert property ((!wire_busy && enable && !(access_size inside {3'b000,3'b001,3'b010,3'b011,3'b100,3'b101})) |-> ##0 (reg_counter==6'd0));

  // reg_counter decrement behavior when not loading a new request
  a_cnt_dec:        assert property ((wire_busy || !enable) |-> ##0
                                     (reg_counter == (($past(reg_counter)==0) ? 6'd0 : $past(reg_counter)-6'd1)));

  // Boundary relations of counter to busy/output
  a_cnt1_boundary:  assert property ((reg_counter==6'd1) |-> (wire_output && !busy));
  a_cnt0_boundary:  assert property ((reg_counter==6'd0) |-> (!wire_output && !busy));

  // reg_cur_addr update rules
  a_addr_inc_busy:  assert property (wire_busy               |-> ##0 (reg_cur_addr == $past(reg_cur_addr) + 32'd4));
  a_addr_load_new:  assert property ((!wire_busy && enable)  |-> ##0 (reg_cur_addr == $past(addr) - START_ADDR));
  a_addr_hold_idle: assert property ((!wire_busy && !enable) |-> ##0 (reg_cur_addr == $past(reg_cur_addr)));

  // Read data mapping and pc update
  a_pc_on_read:     assert property ((wire_output && !reg_rw) |-> ##0 (pc == reg_cur_addr + START_ADDR));
  a_read_byte:      assert property ((wire_output && !reg_rw && access_size==3'b100) |-> ##0
                                     (dout[31:8]==24'h0 && dout[7:0]==mem[reg_cur_addr]));
  a_read_half:      assert property ((wire_output && !reg_rw && access_size==3'b101) |-> ##0
                                     (dout[31:16]==16'h0 &&
                                      dout[15:8]==mem[reg_cur_addr] &&
                                      dout[7:0]==mem[reg_cur_addr+1]));
  // For all others (including 000/001/010/011), 32-bit big-endian read
  a_read_word:      assert property ((wire_output && !reg_rw && !(access_size inside {3'b100,3'b101})) |-> ##0
                                     (dout[31:24]==mem[reg_cur_addr]   &&
                                      dout[23:16]==mem[reg_cur_addr+1] &&
                                      dout[15:8] ==mem[reg_cur_addr+2] &&
                                      dout[7:0]  ==mem[reg_cur_addr+3]));

  // dout must be X when not producing read data
  a_dout_x:         assert property ((!(wire_output && !reg_rw)) |-> ##0 $isunknown(dout));

  // Write data mapping (use next-cycle check to avoid NBA races)
  a_write_byte:     assert property ((wire_output && reg_rw && access_size==3'b100) |=> (mem[reg_cur_addr]   == $past(reg_din[7:0])));
  a_write_half:     assert property ((wire_output && reg_rw && access_size==3'b101) |=> (mem[reg_cur_addr]   == $past(reg_din[15:8]) &&
                                                                                         mem[reg_cur_addr+1] == $past(reg_din[7:0])));
  a_write_word:     assert property ((wire_output && reg_rw && !(access_size inside {3'b100,3'b101})) |=> (
                                       mem[reg_cur_addr]   == $past(reg_din[31:24]) &&
                                       mem[reg_cur_addr+1] == $past(reg_din[23:16]) &&
                                       mem[reg_cur_addr+2] == $past(reg_din[15:8])  &&
                                       mem[reg_cur_addr+3] == $past(reg_din[7:0])));

  // Address bounds checks during active access
  // Note: mem is declared [0:MEMSIZE], so last valid index is MEMSIZE
  a_bounds_read_b:  assert property ((wire_output && !reg_rw && access_size==3'b100) |-> (reg_cur_addr              <= MEMSIZE));
  a_bounds_read_h:  assert property ((wire_output && !reg_rw && access_size==3'b101) |-> (reg_cur_addr + 32'd1      <= MEMSIZE));
  a_bounds_read_w:  assert property ((wire_output && !reg_rw && !(access_size inside {3'b100,3'b101})) |-> (reg_cur_addr + 32'd3 <= MEMSIZE));

  a_bounds_write_b: assert property ((wire_output && reg_rw && access_size==3'b100) |-> (reg_cur_addr              <= MEMSIZE));
  a_bounds_write_h: assert property ((wire_output && reg_rw && access_size==3'b101) |-> (reg_cur_addr + 32'd1      <= MEMSIZE));
  a_bounds_write_w: assert property ((wire_output && reg_rw && !(access_size inside {3'b100,3'b101})) |-> (reg_cur_addr + 32'd3 <= MEMSIZE));

  // Coverage
  c_read_000:  cover property (wire_output && !reg_rw && access_size==3'b000);
  c_read_001:  cover property (wire_output && !reg_rw && access_size==3'b001);
  c_read_010:  cover property (wire_output && !reg_rw && access_size==3'b010);
  c_read_011:  cover property (wire_output && !reg_rw && access_size==3'b011);
  c_read_100:  cover property (wire_output && !reg_rw && access_size==3'b100);
  c_read_101:  cover property (wire_output && !reg_rw && access_size==3'b101);

  c_write_000: cover property (wire_output && reg_rw && access_size==3'b000);
  c_write_001: cover property (wire_output && reg_rw && access_size==3'b001);
  c_write_010: cover property (wire_output && reg_rw && access_size==3'b010);
  c_write_011: cover property (wire_output && reg_rw && access_size==3'b011);
  c_write_100: cover property (wire_output && reg_rw && access_size==3'b100);
  c_write_101: cover property (wire_output && reg_rw && access_size==3'b101);

  c_busy_pulse: cover property ((!wire_busy && enable && access_size==3'b001) ##1 busy ##[1:$] !busy);
  c_illegal_asz: cover property ((!wire_busy && enable && !(access_size inside {3'b000,3'b001,3'b010,3'b011,3'b100,3'b101}))
                                 ##1 (!wire_output && !busy));
  c_cnt1_phase: cover property (reg_counter==6'd1 && wire_output && !busy);
endmodule

bind mips_memory2 mips_memory2_sva #(.MEMSIZE(MEMSIZE), .START_ADDR(START_ADDR)) mips_memory2_sva_i();