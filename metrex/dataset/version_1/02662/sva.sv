// SVA checker for register_module
// Bind this to the DUT and provide a sampling clock/reset from the TB.

module register_module_sva #(
  parameter int NUMBER_INTERFACE_REGS = 16,
  parameter int MB_REG_START          = 3
)(
  input  logic                              clk,
  input  logic                              rst_n,
  input  logic [31:0]                       interface_from_core_fp,
  input  logic                              mb_reg_rwn,
  input  logic [15:0]                       mb_reg_select,
  input  logic [31:0]                       mb_reg_output,
  input  logic [NUMBER_INTERFACE_REGS-1:MB_REG_START] mb_reg_wr,
  input  logic [NUMBER_INTERFACE_REGS-1:MB_REG_START] mb_reg_rd,
  input  logic [31:0]                       mb_reg_out_w [NUMBER_INTERFACE_REGS-1:MB_REG_START]
);

  localparam int LO = MB_REG_START;
  localparam int HI = NUMBER_INTERFACE_REGS-1;

  wire [HI:LO] sel_mask = mb_reg_select[HI:LO];

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Sanity on controls
  ap_no_x_ctrl:     assert property (!$isunknown({mb_reg_rwn, sel_mask}));
  // No selects below supported address range
  generate if (LO > 0) begin
    ap_low_sel_zero: assert property (mb_reg_select[LO-1:0] == '0);
  end endgenerate
  // At most one address selected
  ap_onehot:        assert property ($onehot0(sel_mask));

  // No-select implies no rd/wr activity
  ap_idle_zero:     assert property ((sel_mask == '0) |-> (mb_reg_rd == '0 && mb_reg_wr == '0));

  // Output passthrough when read or when no select
  ap_out_passthru:  assert property ((mb_reg_rwn || (sel_mask == '0)) |-> mb_reg_output == interface_from_core_fp);

  // Per-address checks and coverage
  generate
    genvar i;
    for (i = LO; i <= HI; i++) begin : PER_ADDR

      // Exact decode for rd/wr bits
      ap_rd_eq: assert property (mb_reg_rd[i] == (mb_reg_select[i] &  mb_reg_rwn));
      ap_wr_eq: assert property (mb_reg_wr[i] == (mb_reg_select[i] & !mb_reg_rwn));
      ap_rd_wr_mutex: assert property (!(mb_reg_rd[i] && mb_reg_wr[i]));

      // When reading (rwn==1) and selected, shadow equals interface bus
      ap_shadow_update_on_read: assert property (mb_reg_select[i] &&  mb_reg_rwn |-> mb_reg_out_w[i] == interface_from_core_fp);

      // When writing (rwn==0) and selected, output drives selected shadow
      ap_out_on_write:          assert property (mb_reg_select[i] && !mb_reg_rwn |-> mb_reg_output == mb_reg_out_w[i]);

      // Coverage: observe read/write for each address and read<->write transitions
      cp_read_i:      cover property (mb_reg_select[i] &&  mb_reg_rwn);
      cp_write_i:     cover property (mb_reg_select[i] && !mb_reg_rwn);
      cp_r2w_i:       cover property (mb_reg_select[i] &&  mb_reg_rwn ##1 mb_reg_select[i] && !mb_reg_rwn);
      cp_w2r_i:       cover property (mb_reg_select[i] && !mb_reg_rwn ##1 mb_reg_select[i] &&  mb_reg_rwn);

    end
  endgenerate

  // Global coverage
  cp_idle:  cover property (sel_mask == '0);
  cp_any_r: cover property (|sel_mask &&  mb_reg_rwn);
  cp_any_w: cover property (|sel_mask && !mb_reg_rwn);

endmodule

// Example bind (adjust clk/rst names to your TB)
// bind register_module register_module_sva #(
//   .NUMBER_INTERFACE_REGS(NUMBER_INTERFACE_REGS),
//   .MB_REG_START(MB_REG_START)
// ) u_sva ( .clk(tb_clk), .rst_n(tb_rst_n),
//   .interface_from_core_fp(interface_from_core_fp),
//   .mb_reg_rwn(mb_reg_rwn),
//   .mb_reg_select(mb_reg_select),
//   .mb_reg_output(mb_reg_output),
//   .mb_reg_wr(mb_reg_wr),
//   .mb_reg_rd(mb_reg_rd),
//   .mb_reg_out_w(mb_reg_out_w)
// );