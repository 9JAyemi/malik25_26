// SVA for nios_system_switches
// Bind into the DUT scope to access internal nets (read_mux_out, data_in, clk_en)

module nios_system_switches_sva (
  input logic         clk,
  input logic         reset_n,
  input logic [1:0]   address,
  input logic [7:0]   in_port,
  input logic [7:0]   data_in,
  input logic [7:0]   read_mux_out,
  input logic         clk_en,
  input logic [31:0]  readdata
);

  default clocking cb @(posedge clk); endclocking

  // Combinational wiring checks (sampled on clk for simplicity)
  assert property (data_in == in_port);

  // Mux function check (covers 00/11 same behavior)
  assert property (
    read_mux_out ==
      (address == 2'b00 ? data_in :
       address == 2'b01 ? {1'b0,  data_in[7:1]} :
       address == 2'b10 ? {2'b00, data_in[7:2]} :
                          data_in)
  );

  // clk_en must be constantly 1
  assert property (clk_en);

  // While in reset, output must be 0
  assert property (!reset_n |-> readdata == 32'h0);

  // Upper 24 bits are always zero (both during and after reset)
  assert property (readdata[31:8] == 24'h0);

  // Registered behavior: on each enabled cycle, readdata reflects prior-cycle read_mux_out
  // Guard with $past(reset_n) to avoid X on first active cycle
  assert property (disable iff (!reset_n)
                   $past(reset_n) & $past(clk_en) |-> readdata == {24'h0, $past(read_mux_out)});

  // No unknowns on output when out of reset
  assert property (reset_n |-> !$isunknown(readdata));

  // --------------- Coverage ---------------

  // Reset deassertion observed
  cover property (!reset_n ##1 reset_n);

  // Exercise all address selections
  cover property (reset_n && address == 2'b00);
  cover property (reset_n && address == 2'b01);
  cover property (reset_n && address == 2'b10);
  cover property (reset_n && address == 2'b11);

  // Observe a register update consistent with mux output
  cover property ($past(reset_n) && reset_n &&
                  readdata == {24'h0, $past(read_mux_out)});

endmodule

bind nios_system_switches nios_system_switches_sva sva_i (.*);