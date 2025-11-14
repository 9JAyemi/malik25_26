// SVA for register_interface
// Bindable checker that also peeks the internal memory via ref port

module register_interface_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic        reg_req,
  input  logic        reg_rd_wr_L,    // 1=write, 0=read
  input  logic [7:0]  reg_addr,
  input  logic [31:0] reg_wr_data,
  input  logic [31:0] reg_rd_data,
  input  logic        reg_ack,
  ref    logic [31:0] register [255:0]
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset)

  // Reset behavior (not disabled on reset)
  a_reset_vals: assert property (@(posedge clk) reset |-> (reg_ack==0 && reg_rd_data==32'd0));

  // Ack semantics
  a_ack_on_valid_req:  assert property (reg_req && (reg_addr <= 8'hFF) |-> reg_ack);
  a_ack_rise_only_on_req: assert property ($rose(reg_ack) |-> (reg_req && (reg_addr <= 8'hFF)));
  a_ack_changes_only_on_req_or_reset: assert property (@(posedge clk) $changed(reg_ack) |-> (reset || reg_req));
  a_ack_stable_when_no_req: assert property (!reg_req |-> $stable(reg_ack));

  // Read/write data semantics
  a_write_keeps_rd_data_stable: assert property (reg_req && reg_rd_wr_L |-> $stable(reg_rd_data));
  a_read_returns_mem:           assert property (reg_req && !reg_rd_wr_L |-> reg_rd_data == $past(register[reg_addr]));
  a_write_updates_mem_next:     assert property (reg_req && reg_rd_wr_L |=> register[$past(reg_addr)] == $past(reg_wr_data));

  // Invalid address branch (unreachable with 8-bit addr, but specified)
  a_invalid_addr_no_ack_and_zero: assert property (reg_req && (reg_addr > 8'hFF) |-> (!reg_ack && (reg_rd_data==32'd0)));

  // X-protection
  a_inputs_known_on_req: assert property (reg_req |-> !$isunknown({reg_rd_wr_L, reg_addr, reg_wr_data}));
  a_outputs_known:       assert property (!$isunknown({reg_ack, reg_rd_data}));

  // Functional covers
  c_write:  cover property (reg_req && reg_rd_wr_L && reg_ack);
  c_read:   cover property (reg_req && !reg_rd_wr_L && reg_ack);
  c_wr_rd_same_addr_next: cover property (reg_req && reg_rd_wr_L ##1 reg_req && !reg_rd_wr_L && (reg_addr == $past(reg_addr)));
  c_b2b_writes: cover property (reg_req && reg_rd_wr_L ##1 reg_req && reg_rd_wr_L);
  c_b2b_reads:  cover property (reg_req && !reg_rd_wr_L ##1 reg_req && !reg_rd_wr_L);

endmodule

bind register_interface register_interface_sva sva_i (
  .clk(clk),
  .reset(reset),
  .reg_req(reg_req),
  .reg_rd_wr_L(reg_rd_wr_L),
  .reg_addr(reg_addr),
  .reg_wr_data(reg_wr_data),
  .reg_rd_data(reg_rd_data),
  .reg_ack(reg_ack),
  .register(register)
);