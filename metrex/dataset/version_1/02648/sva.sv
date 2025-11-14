// SVA for nios_system_keys
// Bindable, concise, and checks key functionality and coverage.

`ifndef NIOS_SYSTEM_KEYS_SVA
`define NIOS_SYSTEM_KEYS_SVA

module nios_system_keys_sva
(
  input logic         clk,
  input logic         reset_n,
  input logic  [1:0]  address,
  input logic  [3:0]  in_port,
  input logic [31:0]  readdata,
  input logic         clk_en,
  input logic  [3:0]  data_in,
  input logic  [3:0]  read_mux_out
);

  // Sanity/X checks
  assert property (@(posedge clk) !$isunknown(reset_n))
    else $error("reset_n is X/Z");

  assert property (@(posedge clk) disable iff(!reset_n) !$isunknown({address,in_port}))
    else $error("address/in_port X/Z when active");

  assert property (@(posedge clk) disable iff(!reset_n) !$isunknown(readdata))
    else $error("readdata X/Z when active");

  // Combinational correctness
  assert property (@(posedge clk) data_in == in_port)
    else $error("data_in != in_port");

  assert property (@(posedge clk)
                   read_mux_out == ({4{address==2'd0}} & data_in))
    else $error("read_mux_out decode mismatch");

  // clk_en is hard-1
  assert property (@(posedge clk) clk_en)
    else $error("clk_en deasserted");

  // Reset behavior: while reset is low, output is zero
  assert property (@(posedge clk) !reset_n |-> readdata == 32'd0)
    else $error("readdata not zero during reset");

  // Registered update: next-cycle equals zero-extended mux
  assert property (@(posedge clk) disable iff(!reset_n)
                   readdata == $past({28'd0, read_mux_out}))
    else $error("readdata next-cycle mismatch");

  // High bits must always be zero (zero-extension)
  assert property (@(posedge clk) readdata[31:4] == 28'd0)
    else $error("readdata[31:4] not zero");

  // No glitching between clocks (except during async reset)
  assert property (@(negedge clk) reset_n |-> $stable(readdata))
    else $error("readdata glitches between clocks");

  // Functional coverage
  cover property (@(posedge clk) $fell(reset_n));
  cover property (@(posedge clk) $rose(reset_n));

  cover property (@(posedge clk) disable iff(!reset_n) address==2'd0);
  cover property (@(posedge clk) disable iff(!reset_n) address!=2'd0);

  // Cover that a read at addr 0 captures in_port
  cover property (@(posedge clk) disable iff(!reset_n)
                  (address==2'd0) ##1 (readdata[3:0] == $past(in_port)));

  // Cover that a read at nonzero addr yields zero
  cover property (@(posedge clk) disable iff(!reset_n)
                  (address!=2'd0) ##1 (readdata == 32'd0));

endmodule

bind nios_system_keys nios_system_keys_sva sva_i(.*);

`endif