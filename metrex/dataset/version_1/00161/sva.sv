// SVA for mig_7series_v4_0_axi_mc_wrap_cmd
// Bind these assertions to the DUT. Focus: register updates, counters, pending logic, ignore flags, and param-dependent behavior.

module mig_7series_v4_0_axi_mc_wrap_cmd_sva #(
  parameter integer C_AXI_ADDR_WIDTH = 32,
  parameter integer C_MC_ADDR_WIDTH  = 30,
  parameter integer C_MC_BURST_LEN   = 1,
  parameter integer C_DATA_WIDTH     = 32,
  parameter integer C_AXSIZE         = 2,
  parameter integer C_MC_RD_INST     = 0
)(
  input  wire                                 clk,
  input  wire                                 reset,
  input  wire [C_AXI_ADDR_WIDTH-1:0]          axaddr,
  input  wire [7:0]                           axlen,
  input  wire [2:0]                           axsize,
  input  wire                                 axhandshake,
  input  wire                                 next,
  input  wire [C_AXI_ADDR_WIDTH-1:0]          cmd_byte_addr,
  input  wire                                 ignore_begin,
  input  wire                                 ignore_end,
  input  wire                                 next_pending,

  // Internal DUT signals (brought out for SVA via bind)
  input  wire [3:0]                           axlen_cnt,
  input  wire [3:0]                           int_addr,
  input  wire                                 sel_first_r,
  input  wire                                 int_next_pending_r,
  input  wire [3:0]                           axlen_cnt_t,
  input  wire [3:0]                           axlen_cnt_i,
  input  wire [3:0]                           int_addr_t,
  input  wire [3:0]                           int_addr_p,
  input  wire [3:0]                           int_addr_t_inc,
  input  wire                                 extra_cmd,
  input  wire                                 addr_offset,
  input  wire                                 sel_first,
  input  wire                                 int_next_pending
);

  localparam int AW = C_AXI_ADDR_WIDTH;

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Basic resets
  ap_reset_int_addr:        assert property ($rose(reset) |=> int_addr == 4'h0);
  ap_reset_axlen_cnt:       assert property ($rose(reset) |=> axlen_cnt == 4'hf);
  ap_reset_next_pend_r:     assert property ($rose(reset) |=> int_next_pending_r == 1'b1);
  ap_reset_sel_first_r:     assert property ($rose(reset) |=> sel_first_r == 1'b0);

  // Address composition invariants
  ap_addr_low_bits:         assert property (cmd_byte_addr[C_AXSIZE-1:0] == axaddr[C_AXSIZE-1:0]);
  ap_addr_mid_nibble:       assert property (cmd_byte_addr[C_AXSIZE+3:C_AXSIZE] == int_addr_t[3:0]);
  ap_addr_high_bits:        assert property (cmd_byte_addr[AW-1:C_AXSIZE+4] == axaddr[AW-1:C_AXSIZE+4]);

  // int_addr sequencing
  ap_load_int_addr_on_hs:   assert property (axhandshake && !next |=> int_addr == axaddr[C_AXSIZE +: 4]);
  ap_inc_int_addr_on_next:  assert property (next |=> int_addr == int_addr_p);

  // axlen_cnt sequencing
  ap_load_len_on_hs:        assert property (axhandshake && !next |=> axlen_cnt == axlen_cnt_i);
  ap_dec_len_on_next:       assert property (next |=> axlen_cnt == (axlen_cnt_t - 1'b1));
  ap_len_no_underflow:      assert property (next |-> (axlen_cnt_t != 4'h0));

  // Pending logic
  ap_int_next_pending_def:  assert property (int_next_pending == (|axlen_cnt_t));
  ap_next_pending_mux0:     assert property (!extra_cmd |-> next_pending == int_next_pending);
  ap_next_pending_mux1:     assert property ( extra_cmd |-> next_pending == int_next_pending_r);

  // int_next_pending_r update/hold
  ap_np_r_updates:          assert property (extra_cmd && next |=> int_next_pending_r == int_next_pending);
  ap_np_r_stable_else:      assert property (!(extra_cmd && next) |=> $stable(int_next_pending_r));

  // ignore flags
  ap_ignore_begin_eq:       assert property (ignore_begin == (sel_first ? addr_offset : 1'b0));
  ap_ignore_end_eq:         assert property (ignore_end   == (next_pending ? 1'b0     : addr_offset));
  ap_ignore_begin_imp:      assert property (ignore_begin |-> sel_first && addr_offset);
  ap_ignore_end_imp:        assert property (ignore_end   |-> !next_pending && addr_offset);

  // sel_first_r sequencing and sel_first combine
  ap_sel_first_r_set:       assert property (axhandshake && !next |=> sel_first_r);
  ap_sel_first_r_clr:       assert property (next |=> !sel_first_r);
  ap_sel_first_def:         assert property (sel_first == (axhandshake || sel_first_r));

  // Arithmetic/transform invariants
  ap_int_addr_t_inc:        assert property (int_addr_t_inc == (int_addr_t + C_MC_BURST_LEN));
  ap_int_addr_p_def:        assert property (int_addr_p == ((int_addr_t & ~axlen[3:0]) | (int_addr_t_inc & axlen[3:0])));

  // Parameter-specific checks
  generate
    if (C_MC_BURST_LEN == 1) begin
      ap_addr_offset_zero:  assert property (addr_offset == 1'b0);
      ap_extra_cmd_zero:    assert property (extra_cmd   == 1'b0);
      ap_np_eq_intnp:       assert property (next_pending == int_next_pending);
      ap_len_i_eq_axlen:    assert property (axlen_cnt_i == axlen[3:0]);
      ap_int_addr_t_sel:    assert property (int_addr_t == (axhandshake ? axaddr[C_AXSIZE +: 4] : int_addr));
    end else begin
      ap_addr_offset_bit:   assert property (addr_offset == axaddr[C_AXSIZE]);
      ap_len_i_shift:       assert property (axlen_cnt_i == (axlen[3:0] >> 1));
      if (C_MC_RD_INST == 0) begin
        ap_int_addr_t_hold: assert property (int_addr_t == int_addr);
      end else begin
        ap_int_addr_t_sel2: assert property (int_addr_t == (axhandshake ? axaddr[C_AXSIZE +: 4] : int_addr));
      end
    end
  endgenerate

  // Expected last-beat behavior (no extra_cmd path)
  ap_last_beat_clears_np:   assert property (next && !extra_cmd && (axlen_cnt_t == 4'h1) |=> !next_pending);

  // Covers
  cp_hs_only:               cover property (axhandshake && !next);
  cp_hs_and_next_same:      cover property (axhandshake && next);
  cp_last_beat:             cover property (next && (axlen_cnt_t == 4'h1));
  cp_ignore_begin:          cover property (ignore_begin);
  cp_ignore_end:            cover property (ignore_end);
  cp_extra_cmd_update:      cover property (extra_cmd && next);
  cp_two_steps_addr:        cover property (next ##1 next && (int_addr != $past(int_addr,2)));

endmodule

// Bind example (instantiate in your testbench once; parameters are inherited)
// bind mig_7series_v4_0_axi_mc_wrap_cmd
//   mig_7series_v4_0_axi_mc_wrap_cmd_sva #(
//     .C_AXI_ADDR_WIDTH(C_AXI_ADDR_WIDTH),
//     .C_MC_ADDR_WIDTH (C_MC_ADDR_WIDTH ),
//     .C_MC_BURST_LEN  (C_MC_BURST_LEN  ),
//     .C_DATA_WIDTH    (C_DATA_WIDTH    ),
//     .C_AXSIZE        (C_AXSIZE        ),
//     .C_MC_RD_INST    (C_MC_RD_INST    )
//   ) sva (.*);