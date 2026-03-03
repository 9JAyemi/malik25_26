// SVA for pio_latency
module pio_latency_sva (
  input  logic        clk,
  input  logic        reset_n,
  input  logic [1:0]  address,
  input  logic [15:0] in_port,
  input  logic [15:0] readdata,
  input  logic [15:0] data_in,
  input  logic [15:0] read_mux_out,
  input  logic        clk_en
);
  default clocking cb @(posedge clk); endclocking

  // Basic integrity
  a_no_x_inputs:   assert property (disable iff (!reset_n) !$isunknown({address,in_port,clk_en}));
  a_no_x_outputs:  assert property (disable iff (!reset_n) !$isunknown({readdata,read_mux_out,data_in}));

  // Known constants/mappings
  a_clken_const:   assert property (clk_en);
  a_data_in_map:   assert property (data_in == in_port);

  // Read mux correctness
  a_mux_sel0:      assert property ((address == 2'b00) |-> (read_mux_out == data_in));
  a_mux_selnz:     assert property ((address != 2'b00) |-> (read_mux_out == 16'h0000));

  // Register update behavior
  a_reg_updates:   assert property (disable iff (!reset_n) clk_en |-> (readdata == read_mux_out));
  a_hold_when_gated: assert property (disable iff (!reset_n) !clk_en |-> (readdata == $past(readdata)));

  // Reset behavior (async clear holds 0 while low; checked on clock)
  a_reset_holds_zero: assert property (@(posedge clk) !reset_n |-> (readdata == 16'h0000));

  // Functional coverage
  c_sel0_nonzero:  cover property (disable iff (!reset_n) (address == 2'b00) && (in_port != 16'h0000) && (readdata == in_port));
  c_selnz_zero:    cover property (disable iff (!reset_n) (address != 2'b00) && (readdata == 16'h0000));
  c_addr_toggle:   cover property (disable iff (!reset_n) (address == 2'b00) ##1 (address != 2'b00) ##1 (address == 2'b00));
  c_data_change_cap: cover property (disable iff (!reset_n) (address == 2'b00) && $changed(in_port) && (readdata == in_port));
endmodule

// Bind into DUT
bind pio_latency pio_latency_sva sva_pio_latency (
  .clk(clk),
  .reset_n(reset_n),
  .address(address),
  .in_port(in_port),
  .readdata(readdata),
  .data_in(data_in),
  .read_mux_out(read_mux_out),
  .clk_en(clk_en)
);