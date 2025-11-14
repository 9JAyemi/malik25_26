// SVA for the provided registers and muxes.
// Bind these to the DUT; focuses on key functional checks with concise properties.

// ---------- reg32 ----------
module reg32_sva(input clk, input clr, input write_enable, input [31:0] write_value, input [31:0] Rout);
  default clocking cb @(posedge clk); endclocking

  // Controls not X at clock edge
  assert property (cb !$isunknown({clr, write_enable}));

  // Functional: write dominates clear if both asserted
  assert property (cb write_enable |=> Rout == $past(write_value));
  assert property (cb clr && !write_enable |=> Rout == 32'h0);
  assert property (cb !clr && !write_enable |=> Rout == $past(Rout));

  // Coverage
  cover property (cb clr && !write_enable);
  cover property (cb write_enable && !clr);
  cover property (cb write_enable && clr);
  cover property (cb !write_enable && !clr);
endmodule
bind reg32 reg32_sva u_reg32_sva (.*);

// ---------- reg32_R0 ----------
module reg32_R0_sva(input clk, input clr, input write_enable, input BA_out, input [31:0] write_value, input [31:0] Rout);
  default clocking cb @(posedge clk); endclocking

  assert property (cb !$isunknown({clr, write_enable, BA_out}));

  // Functional: mask by ~BA_out on write; write dominates clear
  assert property (cb write_enable |=> Rout == ($past(write_value) & {32{~$past(BA_out)}}));
  assert property (cb clr && !write_enable |=> Rout == 32'h0);
  assert property (cb !clr && !write_enable |=> Rout == $past(Rout));
  // Explicit BA_out=1 gate => zero on write
  assert property (cb write_enable && BA_out |=> Rout == 32'h0);

  // Coverage
  cover property (cb write_enable && !BA_out);
  cover property (cb write_enable && BA_out);
  cover property (cb clr && !write_enable);
  cover property (cb !clr && !write_enable);
endmodule
bind reg32_R0 reg32_R0_sva u_reg32_R0_sva (.*);

// ---------- reg32_MDR ----------
module reg32_MDR_sva(
  input clk, input clr,
  input MDR_write_enable, input Memory_write_enable, input Memory_read_enable,
  input [31:0] Bus_input, input [31:0] Memory_input,
  input [31:0] Bus_output, input [31:0] Memory_output,
  input Mem_RW,
  input [31:0] Rout
);
  default clocking cb @(posedge clk); endclocking

  assert property (cb !$isunknown({clr, MDR_write_enable, Memory_write_enable, Memory_read_enable}));

  // Mem_RW definition
  assert property (cb Mem_RW == (MDR_write_enable && !Memory_read_enable));

  // MDR register behavior: write (from selected source), clear-only, hold
  assert property (cb MDR_write_enable
                   |=> Rout == $past(Memory_read_enable ? Memory_input : Bus_input));
  assert property (cb clr && !MDR_write_enable |=> Rout == 32'h0);
  assert property (cb !clr && !MDR_write_enable |=> Rout == $past(Rout));

  // Output mux behavior
  assert property (cb Memory_write_enable |-> (Memory_output == Rout && Bus_output == 32'h0));
  assert property (cb !Memory_write_enable |-> (Bus_output == Rout && Memory_output == 32'h0));

  // Coverage: read path write, bus path write, memory out enable/disable
  cover property (cb MDR_write_enable && Memory_read_enable);
  cover property (cb MDR_write_enable && !Memory_read_enable);
  cover property (cb Memory_write_enable);
  cover property (cb !Memory_write_enable);
  cover property (cb clr && !MDR_write_enable);
endmodule
bind reg32_MDR reg32_MDR_sva u_reg32_MDR_sva (.*);

// ---------- reg32_MAR ----------
module reg32_MAR_sva(input clk, input clr, input write_enable, input [31:0] write_value, input [8:0] Rout);
  default clocking cb @(posedge clk); endclocking

  assert property (cb !$isunknown({clr, write_enable}));

  // Sequential behavior observed on output slice
  assert property (cb write_enable |=> Rout == $past(write_value[8:0]));
  assert property (cb clr && !write_enable |=> Rout == 9'h0);
  assert property (cb !clr && !write_enable |=> Rout == $past(Rout));

  // Coverage
  cover property (cb write_enable);
  cover property (cb clr && !write_enable);
  cover property (cb !clr && !write_enable);
endmodule
bind reg32_MAR reg32_MAR_sva u_reg32_MAR_sva (.*);

// ---------- reg64 ----------
module reg64_sva(
  input clk, input clr, input write_enable,
  input [63:0] input_value,
  input [31:0] Rout_hi, input [31:0] Rout_low
);
  default clocking cb @(posedge clk); endclocking

  assert property (cb !$isunknown({clr, write_enable}));

  // Write dominates clear; clear-only; hold
  assert property (cb write_enable |=> {Rout_hi, Rout_low} == $past(input_value));
  assert property (cb clr && !write_enable |=> Rout_hi == 32'h0 && Rout_low == 32'h0);
  assert property (cb !clr && !write_enable |=> {Rout_hi, Rout_low} == $past({Rout_hi, Rout_low}));

  // Coverage
  cover property (cb write_enable && clr);
  cover property (cb write_enable && !clr);
  cover property (cb clr && !write_enable);
  cover property (cb !write_enable && !clr);
endmodule
bind reg64 reg64_sva u_reg64_sva (.*);

// ---------- MDMux_in (combinational) ----------
module MDMux_in_sva(input clk, input Mem_read_enable, input [31:0] Bus_data, input [31:0] Mdata_in, input [31:0] MDMux_out);
  default clocking cb @(posedge clk); endclocking
  assert property (cb MDMux_out == (Mem_read_enable ? Mdata_in : Bus_data));
  cover  property (cb Mem_read_enable);
  cover  property (cb !Mem_read_enable);
endmodule
bind MDMux_in MDMux_in_sva u_MDMux_in_sva (.*);

// ---------- MDMux_out (combinational) ----------
module MDMux_out_sva(input clk, input Mem_write_enable, input [31:0] MDR_data, input [31:0] BusData_out, input [31:0] Mdata_out);
  default clocking cb @(posedge clk); endclocking
  assert property (cb Mem_write_enable |-> (Mdata_out == MDR_data && BusData_out == 32'h0));
  assert property (cb !Mem_write_enable |-> (BusData_out == MDR_data && Mdata_out == 32'h0));
  cover  property (cb Mem_write_enable);
  cover  property (cb !Mem_write_enable);
endmodule
bind MDMux_out MDMux_out_sva u_MDMux_out_sva (.*)