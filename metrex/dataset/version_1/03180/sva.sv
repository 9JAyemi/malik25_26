// SVA checker for nios_system_charToTransmitter
module nios_system_charToTransmitter_sva (
  input logic        clk,
  input logic        reset_n,
  input logic [1:0]  address,
  input logic [7:0]  in_port,
  input logic [31:0] readdata
);

  // expected mux output (matches DUT intent)
  logic [7:0] exp_mux;
  always_comb exp_mux = (address == 2'd0) ? in_port : 8'h00;

  default clocking cb @(posedge clk); endclocking

  // Basic sanity: no X on inputs while sampling
  a_no_x_inputs: assert property ( !$isunknown({reset_n, address, in_port}) );

  // Asynchronous reset drives readdata to zero immediately
  a_async_reset: assert property (@(negedge reset_n) 1 |-> (readdata == 32'd0));

  // While in reset, output must hold zero
  a_hold_zero_in_reset: assert property ( !reset_n |-> (readdata == 32'd0) );

  // Upper 24 bits must always be zero (design zero-extends 8-bit mux)
  a_upper_zero: assert property ( reset_n |-> (readdata[31:8] == 24'd0) );

  // On each cycle out of reset, next readdata equals previous cycle's mux
  a_update_from_prev_mux: assert property (
    reset_n && $past(reset_n) |-> readdata == {24'd0, $past(exp_mux)}
  );

  // Mux correctness per address selection (checks low byte behavior)
  a_mux_when_sel0: assert property (
    $past(reset_n) && ($past(address) == 2'd0) |-> (readdata[7:0] == $past(in_port))
  );
  a_mux_when_sel_other: assert property (
    $past(reset_n) && ($past(address) != 2'd0) |-> (readdata[7:0] == 8'h00)
  );

  // No X on output when out of reset
  a_no_x_output: assert property ( reset_n |-> !$isunknown(readdata) );

  // Functional coverage
  c_reset_assert:   cover property ( $fell(reset_n) );
  c_reset_release:  cover property ( $rose(reset_n) );

  // Cover both mux paths with observable outcomes
  c_sel0_example: cover property (
    reset_n && (address == 2'd0) && (in_port == 8'hA5)
    ##1 (readdata == 32'h000000A5)
  );
  c_sel_other_example: cover property (
    reset_n && (address != 2'd0) && (in_port != 8'h00)
    ##1 (readdata == 32'h00000000)
  );

  // Cover a non-zero transfer and that upper bits remain zero
  c_nonzero_transfer: cover property (
    reset_n && (address == 2'd0) && (in_port != 8'h00)
    ##1 (readdata[31:8] == 24'h0 && readdata[7:0] == $past(in_port))
  );

endmodule

// Bind SVA to DUT
bind nios_system_charToTransmitter nios_system_charToTransmitter_sva sva_i (
  .clk(clk),
  .reset_n(reset_n),
  .address(address),
  .in_port(in_port),
  .readdata(readdata)
)