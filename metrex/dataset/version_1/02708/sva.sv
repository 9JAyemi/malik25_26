// SVA for niosII_system_switches
// Bindable, concise, with focused checks and coverage

module niosII_system_switches_sva (
  input  logic        clk,
  input  logic        reset_n,
  input  logic [1:0]  address,
  input  logic [7:0]  in_port,
  input  logic [31:0] readdata,
  input  logic [7:0]  data_in,
  input  logic [7:0]  read_mux_out,
  input  logic        clk_en
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!reset_n)

  function automatic logic [31:0] exp_word (input logic [1:0] a, input logic [7:0] d);
    exp_word = (a == 2'b11) ? {d,d,d,d} : {24'h0, d};
  endfunction

  // Basic structural checks
  a_clk_en_const:        assert property (clk_en);
  a_data_in_passthrough: assert property (data_in == in_port);
  a_read_mux_out:        assert property (read_mux_out == ((address==2'b00) ? data_in : 8'h00));

  // Asynchronous reset behavior
  a_async_clear_now:     assert property (@(negedge reset_n) ##0 readdata == 32'h0);
  a_zero_while_in_reset: assert property (@(posedge clk) !reset_n |-> readdata == 32'h0);

  // Registered read value matches previous-cycle address/data
  a_readdata_mapping:    assert property ($past(reset_n) |-> readdata == exp_word($past(address), $past(data_in)));

  // Sanity: no X on key IOs and outputs when not in reset
  a_no_x_inputs:         assert property (!$isunknown({address, in_port, clk_en}));
  a_no_x_readdata:       assert property (!$isunknown(readdata));

  // Targeted coverage
  c_reset_seq:           cover property (@(posedge clk) !reset_n ##1 reset_n);
  c_addr00:              cover property (address==2'b00);
  c_addr01:              cover property (address==2'b01);
  c_addr10:              cover property (address==2'b10);
  c_addr11:              cover property (address==2'b11);
  c_map_00:              cover property ($past(reset_n) && $past(address)==2'b00 && readdata=={24'h0,$past(data_in)});
  c_map_11:              cover property ($past(reset_n) && $past(address)==2'b11 && readdata=={4{$past(data_in)}});

endmodule

// Bind into DUT
bind niosII_system_switches niosII_system_switches_sva sva_i (
  .clk(clk),
  .reset_n(reset_n),
  .address(address),
  .in_port(in_port),
  .readdata(readdata),
  .data_in(data_in),
  .read_mux_out(read_mux_out),
  .clk_en(clk_en)
);