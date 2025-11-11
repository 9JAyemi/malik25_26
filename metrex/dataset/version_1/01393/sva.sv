// SVA for wb_mcb_32
// Bindable checker with concise yet comprehensive protocol and data-path checks

module wb_mcb_32_sva (
  input  logic        clk,
  input  logic        rst,

  input  logic [31:0] wb_adr_i,
  input  logic [31:0] wb_dat_i,
  input  logic        wb_we_i,
  input  logic [3:0]  wb_sel_i,
  input  logic        wb_stb_i,
  input  logic        wb_cyc_i,
  input  logic [31:0] wb_dat_o,
  input  logic        wb_ack_o,

  input  logic        mcb_cmd_clk,
  input  logic        mcb_cmd_en,
  input  logic [2:0]  mcb_cmd_instr,
  input  logic [5:0]  mcb_cmd_bl,
  input  logic [31:0] mcb_cmd_byte_addr,
  input  logic        mcb_cmd_empty,
  input  logic        mcb_cmd_full,

  input  logic        mcb_wr_clk,
  input  logic        mcb_wr_en,
  input  logic [3:0]  mcb_wr_mask,
  input  logic [31:0] mcb_wr_data,
  input  logic        mcb_wr_empty,
  input  logic        mcb_wr_full,
  input  logic        mcb_wr_underrun,
  input  logic [6:0]  mcb_wr_count,
  input  logic        mcb_wr_error,

  input  logic        mcb_rd_clk,
  input  logic        mcb_rd_en,
  input  logic [31:0] mcb_rd_data,
  input  logic        mcb_rd_empty,
  input  logic        mcb_rd_full,
  input  logic        mcb_rd_overflow,
  input  logic [6:0]  mcb_rd_count,
  input  logic        mcb_rd_error,

  // internal
  input  logic        cycle_reg
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Reset behavior
  assert property (@cb rst |-> (!wb_ack_o && !mcb_cmd_en && !mcb_wr_en && !cycle_reg && mcb_cmd_instr==3'b000));

  // Clock passthroughs
  assert property (@cb mcb_cmd_clk == clk);
  assert property (@cb mcb_wr_clk  == clk);
  assert property (@cb mcb_rd_clk  == clk);

  // Static/comb connectivity
  assert property (@cb mcb_cmd_bl         == 6'd0);
  assert property (@cb mcb_rd_en          == 1'b1);
  assert property (@cb mcb_cmd_byte_addr  == wb_adr_i);
  assert property (@cb mcb_wr_data        == wb_dat_i);

  // Wishbone handshake sanity
  assert property (@cb wb_ack_o |-> wb_cyc_i);
  assert property (@cb wb_ack_o |=> !wb_ack_o); // single-cycle pulse

  // No new command while a read is pending
  assert property (@cb cycle_reg |-> (!mcb_cmd_en && !mcb_wr_en));

  // Command issuance rules
  assert property (@cb mcb_cmd_en |-> (mcb_cmd_instr==3'b000 || mcb_cmd_instr==3'b001));
  assert property (@cb mcb_cmd_en |-> (wb_cyc_i && wb_stb_i && !wb_ack_o && !cycle_reg));

  // Write transaction: same-cycle cmd, wr_en, ack, mask mapping
  assert property (@cb (wb_cyc_i && wb_stb_i && wb_we_i && !wb_ack_o && !cycle_reg)
                        |-> (mcb_cmd_en && mcb_wr_en && mcb_cmd_instr==3'b000 && wb_ack_o));
  assert property (@cb mcb_wr_en |-> (wb_we_i && mcb_cmd_en && mcb_cmd_instr==3'b000));
  assert property (@cb mcb_wr_en |-> (mcb_wr_mask == ~wb_sel_i));

  // Read transaction: same-cycle cmd (no ack), then ack on data arrival
  assert property (@cb (wb_cyc_i && wb_stb_i && !wb_we_i && !wb_ack_o && !cycle_reg)
                        |-> (mcb_cmd_en && !mcb_wr_en && mcb_cmd_instr==3'b001 && cycle_reg));
  assert property (@cb cycle_reg && mcb_rd_empty |-> !wb_ack_o);
  assert property (@cb $past(cycle_reg) && !mcb_rd_empty
                        |-> (wb_ack_o && !cycle_reg && (wb_dat_o == mcb_rd_data)));

  // Address/data/instr consistency when command asserted
  assert property (@cb mcb_cmd_en |-> (mcb_cmd_byte_addr == wb_adr_i));
  assert property (@cb mcb_cmd_en && mcb_wr_en  |-> mcb_cmd_instr==3'b000);
  assert property (@cb mcb_cmd_en && !mcb_wr_en |-> mcb_cmd_instr==3'b001);

  // Coverage: exercise write, read, masks, back-to-back ops
  cover property (@cb (wb_cyc_i && wb_stb_i && wb_we_i && !cycle_reg)
                       ##0 (mcb_cmd_en && mcb_wr_en && wb_ack_o));
  cover property (@cb (wb_cyc_i && wb_stb_i && !wb_we_i && !cycle_reg)
                       ##0 mcb_cmd_en ##1 cycle_reg ##[1:$] (!mcb_rd_empty) ##0 wb_ack_o);
  cover property (@cb mcb_wr_en && (mcb_wr_mask != 4'h0));
  cover property (@cb (wb_cyc_i && wb_stb_i && wb_we_i && !cycle_reg)
                       ##1 (wb_cyc_i && wb_stb_i && !wb_we_i && !cycle_reg));

endmodule

// Bind into DUT
bind wb_mcb_32 wb_mcb_32_sva sva_inst (
  .clk(clk),
  .rst(rst),

  .wb_adr_i(wb_adr_i),
  .wb_dat_i(wb_dat_i),
  .wb_we_i(wb_we_i),
  .wb_sel_i(wb_sel_i),
  .wb_stb_i(wb_stb_i),
  .wb_cyc_i(wb_cyc_i),
  .wb_dat_o(wb_dat_o),
  .wb_ack_o(wb_ack_o),

  .mcb_cmd_clk(mcb_cmd_clk),
  .mcb_cmd_en(mcb_cmd_en),
  .mcb_cmd_instr(mcb_cmd_instr),
  .mcb_cmd_bl(mcb_cmd_bl),
  .mcb_cmd_byte_addr(mcb_cmd_byte_addr),
  .mcb_cmd_empty(mcb_cmd_empty),
  .mcb_cmd_full(mcb_cmd_full),

  .mcb_wr_clk(mcb_wr_clk),
  .mcb_wr_en(mcb_wr_en),
  .mcb_wr_mask(mcb_wr_mask),
  .mcb_wr_data(mcb_wr_data),
  .mcb_wr_empty(mcb_wr_empty),
  .mcb_wr_full(mcb_wr_full),
  .mcb_wr_underrun(mcb_wr_underrun),
  .mcb_wr_count(mcb_wr_count),
  .mcb_wr_error(mcb_wr_error),

  .mcb_rd_clk(mcb_rd_clk),
  .mcb_rd_en(mcb_rd_en),
  .mcb_rd_data(mcb_rd_data),
  .mcb_rd_empty(mcb_rd_empty),
  .mcb_rd_full(mcb_rd_full),
  .mcb_rd_overflow(mcb_rd_overflow),
  .mcb_rd_count(mcb_rd_count),
  .mcb_rd_error(mcb_rd_error),

  .cycle_reg(cycle_reg)
);