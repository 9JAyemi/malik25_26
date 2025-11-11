// SVA for dual_port_RAM
module dual_port_RAM_sva;

  localparam IDLE = 2'b00;
  localparam W    = 2'b01;
  localparam R    = 2'b10;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Legal state encoding
  assert property (state inside {IDLE, W, R});

  // Reset to IDLE on release
  assert property ($rose(rst_n) |-> state == IDLE);

  // IDLE transitions (priority: write over read)
  assert property (state == IDLE && write_en                  |-> ##1 state == W);
  assert property (state == IDLE && !write_en && read_en      |-> ##1 state == R);
  assert property (state == IDLE && !write_en && !read_en     |-> ##1 state == IDLE);
  assert property (state == IDLE && write_en && read_en       |-> ##1 state == W);

  // W/R must return to IDLE next cycle
  assert property (state == W |-> ##1 state == IDLE);
  assert property (state == R |-> ##1 state == IDLE);

  // Address range on accept (mem depth = 8)
  assert property (state == IDLE && write_en             |-> write_addr < 8);
  assert property (state == IDLE && !write_en && read_en |-> read_addr  < 8);

  // Write capture and commit
  assert property (state == IDLE && write_en
                   |-> ##1 (state == W
                            && write_addr_reg == $past(write_addr)
                            && write_data_reg == $past(write_data)));
  assert property ((state == IDLE && write_en && write_addr < 8)
                   |-> ##1 (mem[$past(write_addr)] == $past(write_data)));

  // Memory must only change in W state
  genvar i;
  generate
    for (i = 0; i < 8; i++) begin : g_mem_stable
      assert property (state != W |-> $stable(mem[i]));
    end
  endgenerate

  // Read timing/value and output update rules
  assert property ((state == IDLE && !write_en && read_en && read_addr < 8)
                   |-> ##1 (state == R && read_data == $past(mem[read_addr])));
  assert property ($changed(read_data) |-> state == R);
  assert property (state == R |-> read_data == read_data_reg);

  // Regs held steady through W
  assert property (state == W |-> (write_addr_reg == $past(write_addr_reg)
                                   && write_data_reg == $past(write_data_reg)));

  // Coverage
  cover property (state == IDLE && write_en ##1 state == W ##1 state == IDLE);
  cover property (state == IDLE && !write_en && read_en ##1 state == R ##1 state == IDLE);
  cover property (state == IDLE && write_en && read_en ##1 state == W);
  // Write then immediate read of same address (data check not enforced here for concision)
  cover property (state == IDLE && write_en && write_addr < 8
                  ##1 state == W
                  ##1 (state == IDLE && !write_en && read_en && read_addr == $past(write_addr,2))
                  ##1 state == R);

endmodule

bind dual_port_RAM dual_port_RAM_sva sva_inst();