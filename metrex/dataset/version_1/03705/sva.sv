// SVA for mem_wb_reg: concise, high-quality checks and coverage
// Bind into the DUT
bind mem_wb_reg mem_wb_reg_sva #(
  .DATA_WIDTH(DATA_WIDTH),
  .INSTRUCTION_WIDTH(INSTRUCTION_WIDTH),
  .REG_ADDR_WIDTH(REG_ADDR_WIDTH)
) u_mem_wb_reg_sva (.*);

module mem_wb_reg_sva
#(
  parameter DATA_WIDTH = 32,
  parameter INSTRUCTION_WIDTH = 32,
  parameter REG_ADDR_WIDTH = 5
)
(
  input clk,
  input rst_n,
  input en,
  input write_back_mux_sel_in,
  input [DATA_WIDTH-1:0] alu_data_in,
  input [DATA_WIDTH-1:0] hi_data_in,
  input [REG_ADDR_WIDTH-1:0] reg_a_wr_addr_in,
  input [REG_ADDR_WIDTH-1:0] reg_b_wr_addr_in,
  input reg_a_wr_en_in,
  input reg_b_wr_en_in,
  input [INSTRUCTION_WIDTH-1:0] instruction_in,

  output write_back_mux_sel_out,
  output [DATA_WIDTH-1:0] alu_data_out,
  output [DATA_WIDTH-1:0] hi_data_out,
  output [REG_ADDR_WIDTH-1:0] reg_a_wr_addr_out,
  output [REG_ADDR_WIDTH-1:0] reg_b_wr_addr_out,
  output reg_a_wr_en_out,
  output reg_b_wr_en_out,
  output [INSTRUCTION_WIDTH-1:0] instruction_out
);

  default clocking cb @(posedge clk); endclocking

  localparam int OUTW = 1 + DATA_WIDTH + DATA_WIDTH + REG_ADDR_WIDTH + REG_ADDR_WIDTH + 1 + 1 + INSTRUCTION_WIDTH;

  logic [OUTW-1:0] out_bus, in_bus;
  assign out_bus = { write_back_mux_sel_out,
                     alu_data_out,
                     hi_data_out,
                     reg_a_wr_addr_out,
                     reg_b_wr_addr_out,
                     reg_a_wr_en_out,
                     reg_b_wr_en_out,
                     instruction_out };

  assign in_bus  = { write_back_mux_sel_in,
                     alu_data_in,
                     hi_data_in,
                     reg_a_wr_addr_in,
                     reg_b_wr_addr_in,
                     reg_a_wr_en_in,
                     reg_b_wr_en_in,
                     instruction_in };

  // Asynchronous reset drives zeros immediately (sample after NBA with ##0)
  assert property (@(negedge rst_n) ##0 (out_bus == '0))
    else $error("mem_wb_reg: outputs not zero on async reset assertion");

  // During reset, outputs must be zero each cycle
  assert property ( !rst_n |-> (out_bus == '0) )
    else $error("mem_wb_reg: outputs not held at zero while in reset");

  // Load inputs on en=1 (1-cycle latency observation due to nonblocking semantics)
  assert property ( disable iff (!rst_n) en |-> (out_bus == $past(in_bus)) )
    else $error("mem_wb_reg: en=1 did not capture inputs");

  // Hold outputs when en=0
  assert property ( disable iff (!rst_n) !en |-> $stable(out_bus) )
    else $error("mem_wb_reg: outputs changed while en=0");

  // Any output change (outside reset) implies en was 1
  assert property ( disable iff (!rst_n) $changed(out_bus) |-> $past(en) )
    else $error("mem_wb_reg: outputs changed without enable");

  // No X/Z on outputs in normal operation; en should be known as well
  assert property ( rst_n |-> (!$isunknown(out_bus) && !$isunknown(en)) )
    else $error("mem_wb_reg: X/Z detected on outputs or en during operation");

  // ------------ Coverage ------------
  // Reset pulse and release observed on clock domain
  cover property ( $fell(rst_n) );
  cover property ( $rose(rst_n) );

  // Observe at least one load cycle
  cover property ( disable iff (!rst_n) en ##1 (out_bus == $past(in_bus)) );

  // Back-to-back loads
  cover property ( disable iff (!rst_n) en and $past(en) );

  // Multi-cycle stall
  cover property ( disable iff (!rst_n) (!en)[*3] );

  // Output change attributed to enable
  cover property ( disable iff (!rst_n) $changed(out_bus) and $past(en) );

endmodule