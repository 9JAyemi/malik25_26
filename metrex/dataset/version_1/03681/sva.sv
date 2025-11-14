// SVA for soc_system_pio_aliveTest_cpu_s0
// Bind-friendly, concise, and high-quality checks

module soc_system_pio_aliveTest_cpu_s0_sva
(
  input  logic        clk,
  input  logic        reset_n,
  input  logic [1:0]  address,
  input  logic        chipselect,
  input  logic        write_n,
  input  logic [31:0] writedata,
  input  logic [1:0]  out_port,
  input  logic [31:0] readdata
);

  default clocking cb @(posedge clk); endclocking

  // Async reset drives storage/output to 0
  assert property (@(negedge reset_n) out_port == 2'b00);

  // During reset, outputs are zeroed
  assert property (@(posedge clk) !reset_n |-> (out_port == 2'b00 && readdata == 32'h0));

  // From here on, disable assertions when in reset
  default disable iff (!reset_n);

  // Upper 30 bits of readdata are always zero
  assert property (readdata[31:2] == 30'b0);

  // Read mux behavior
  assert property ((address == 2'b00) |-> (readdata[1:0] == out_port));
  assert property ((address != 2'b00) |-> (readdata[1:0] == 2'b00));

  // Write to address 0 updates on next cycle
  assert property (chipselect && !write_n && (address == 2'b00)
                   |=> out_port == $past(writedata[1:0]));

  // No write to address 0 => out_port holds value
  assert property (!(chipselect && !write_n && (address == 2'b00))
                   |=> $stable(out_port));

  // Writes to nonzero address must not change out_port
  assert property (chipselect && !write_n && (address != 2'b00)
                   |=> $stable(out_port));

  // Basic X/Z sanitization when not in reset
  assert property (!$isunknown({chipselect, write_n, address, out_port, readdata[1:0]}));

  // Coverage

  // Deassert reset then eventually perform a valid write
  cover property ($rose(reset_n) ##[1:$] (chipselect && !write_n && address == 2'b00));

  // Write followed by correct update
  cover property (chipselect && !write_n && address == 2'b00
                  ##1 out_port == $past(writedata[1:0]));

  // Exercise read at nonzero address returning 0
  cover property (address != 2'b00 && readdata[1:0] == 2'b00);

  // Observe all out_port values
  cover property (out_port == 2'b00);
  cover property (out_port == 2'b01);
  cover property (out_port == 2'b10);
  cover property (out_port == 2'b11);

endmodule

// Example bind (place in a bind file or testbench)
// bind soc_system_pio_aliveTest_cpu_s0 soc_system_pio_aliveTest_cpu_s0_sva
// (.*);