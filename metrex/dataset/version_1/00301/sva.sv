// SVA for nios_system_switches
// Bind into the DUT to check reset, muxing, and registered output behavior.

module nios_system_switches_sva (
  input         clk,
  input         reset_n,
  input  [1:0]  address,
  input  [9:0]  in_port,
  input  [31:0] readdata,
  input         clk_en,
  input  [9:0]  read_mux_out,
  input  [9:0]  data_in
);
  default clocking cb @(posedge clk); endclocking

  // Functional assertions (disabled during reset)
  default disable iff (!reset_n)

  // Inputs/outputs should be known out of reset
  assert property (!$isunknown({address, in_port, readdata})))
    else $error("X/Z detected on address/in_port/readdata");

  // Comb muxing is correct
  assert property (read_mux_out == ((address == 2'b00) ? in_port : 10'b0))
    else $error("read_mux_out does not match address gating");

  // data_in must mirror read_mux_out
  assert property (data_in == read_mux_out)
    else $error("data_in != read_mux_out");

  // clk_en is hard 1'b1 (any change will break the pipeline contract)
  assert property (clk_en)
    else $error("clk_en deasserted");

  // Registered output equals zero-extended selected data from previous cycle
  // Guard with $past(reset_n) to avoid first-cycle-after-reset ambiguity
  assert property ($past(reset_n) |-> 
                   readdata == {22'b0, ($past(address) == 2'b00 ? $past(in_port) : 10'b0)})
    else $error("readdata mismatch vs. prior-cycle selected input");

  // Upper bits must always be zero out of reset
  assert property (readdata[31:10] == '0)
    else $error("readdata upper bits not zero");

  // Reset behavior (checked explicitly and not disabled)
  // After reset assertion, register clears by the next clock
  assert property (@(posedge clk) $fell(reset_n) |-> ##1 (readdata == 32'h0))
    else $error("readdata not cleared 1 cycle after reset assert");

  // While held in reset, register stays at zero
  assert property (@(posedge clk) (!reset_n && $past(!reset_n)) |-> (readdata == 32'h0))
    else $error("readdata changed while in reset");

  // Coverage
  cover property (@(posedge clk) $fell(reset_n) ##1 $rose(reset_n));
  cover property (address == 2'b00 && in_port != 0 ##1 readdata[9:0] == $past(in_port));
  cover property (address != 2'b00 && in_port != 0 ##1 readdata == 32'h0);

endmodule

// Bind into the DUT (internal nets are connected for stronger checking)
bind nios_system_switches nios_system_switches_sva sva_inst (
  .clk         (clk),
  .reset_n     (reset_n),
  .address     (address),
  .in_port     (in_port),
  .readdata    (readdata),
  .clk_en      (clk_en),
  .read_mux_out(read_mux_out),
  .data_in     (data_in)
);