// SVA for wasca_switches
module wasca_switches_sva (
  input        clk,
  input        reset_n,
  input  [1:0] address,
  input  [2:0] in_port,
  input  [2:0] data_in,
  input  [2:0] read_mux_out,
  input [31:0] readdata,
  input        clk_en
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (!reset_n);

  // Constants/connectivity
  a_clk_en_const:    assert property (clk_en);
  a_data_in_conn:    assert property (data_in == in_port);
  a_mux_function:    assert property (read_mux_out == (address == 2'b00 ? data_in : 3'b000));

  // Registered output behavior
  a_upper_zero:      assert property (readdata[31:3] == '0);
  a_reg_update:      assert property ($past(reset_n) && $past(clk_en) |-> readdata == {29'b0, $past(read_mux_out)});
  a_addr_ne0_zero:   assert property ($past(reset_n) && $past(address != 2'b00) |-> readdata == 32'h0);
  a_addr_eq0_match:  assert property ($past(reset_n) && $past(address == 2'b00) |-> readdata[2:0] == $past(in_port));

  // X checks (active out of reset)
  a_xfree_inputs:    assert property (!$isunknown({address, in_port}));
  a_xfree_output:    assert property (!$isunknown(readdata));

  // Reset behavior (not disabled)
  a_reset_clears_next: assert property (@(posedge clk) !reset_n |=> readdata == 32'h0);
  a_async_clear_now:   assert property (@(negedge reset_n) 1'b1 |-> ##0 (readdata == 32'h0));

  // Coverage
  c_addr_both:        cover property (reset_n && address == 2'b00 ##1 address != 2'b00);
  c_capture_change:   cover property (reset_n && address == 2'b00 && $changed(in_port) |=> readdata[2:0] == $past(in_port));
  c_capture_example:  cover property (reset_n && address == 2'b00 && in_port == 3'b101 ##1 readdata[2:0] == 3'b101);
endmodule

bind wasca_switches wasca_switches_sva sva (
  .clk(clk),
  .reset_n(reset_n),
  .address(address),
  .in_port(in_port),
  .data_in(data_in),
  .read_mux_out(read_mux_out),
  .readdata(readdata),
  .clk_en(clk_en)
);