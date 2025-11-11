// SVA for lpf_module: concise, high-signal-quality checks and coverage
// Bind file (place in a separate SVA file and compile with DUT)

module lpf_module_sva (
  input logic                slowest_sync_clk,
  input logic                dcm_locked,
  input logic                aux_reset_in,
  input logic                mb_debug_sys_rst,
  input logic                ext_reset_in,
  input logic                lpf_int,

  // internal DUT signals
  input logic                asr_lpf,
  input logic                lpf_asr,
  input logic                lpf_exr,
  input logic                Q,
  input logic                lpf_int0__0,

  input logic                asr_lpf_reg,
  input logic                lpf_asr_reg,
  input logic                lpf_exr_reg,
  input logic [15:0]         Q_reg,
  input logic [15:0]         lpf_int0__0_reg,
  input logic [15:0]         lpf_int_reg
);

  default clocking cb @(posedge slowest_sync_clk); endclocking

  // Basic connectivity
  assert property (cb 1'b1 |=> asr_lpf == asr_lpf_reg);
  assert property (cb 1'b1 |=> lpf_asr == lpf_asr_reg);
  assert property (cb 1'b1 |=> lpf_exr == lpf_exr_reg);
  assert property (cb 1'b1 |=> Q       == Q_reg[15]);
  assert property (cb 1'b1 |=> lpf_int0__0 == lpf_int0__0_reg[0]);
  assert property (cb 1'b1 |=> lpf_int     == lpf_int_reg[0]);

  // Pipeline correctness
  assert property (cb 1'b1 |=> asr_lpf == $past(dcm_locked));
  assert property (cb 1'b1 |=> lpf_asr == $past(asr_lpf));
  assert property (cb 1'b1 |=> lpf_exr == $past(mb_debug_sys_rst));

  // Zero-shift register must force Q to 0 within 16 cycles, from any time
  assert property (cb 1'b1 |-> ##16 (Q == 1'b0));

  // lpf_int0__0_reg mapping and zero-extend invariant
  assert property (cb 1'b1 |=> lpf_int0__0_reg[15:4] == '0);
  assert property (cb 1'b1 |=> {lpf_int0__0_reg[3], lpf_int0__0_reg[2],
                                lpf_int0__0_reg[1], lpf_int0__0_reg[0]}
                             == $past({Q, lpf_asr, dcm_locked, lpf_exr}));

  // Stage-to-stage transfer
  assert property (cb 1'b1 |=> lpf_int_reg == $past(lpf_int0__0_reg));

  // Output behavior (both outputs are 1-cycle delayed mb_debug_sys_rst path)
  assert property (cb 1'b1 |=> lpf_int0__0 == $past(lpf_exr));
  assert property (cb 1'b1 |=> lpf_int     == $past(lpf_exr));
  assert property (cb 1'b1 |=> lpf_int == lpf_int0__0);

  // Minimal functional coverage
  cover property (cb $rose(dcm_locked)       ##1 asr_lpf ##1 lpf_asr);
  cover property (cb $fell(dcm_locked)       ##1 !asr_lpf ##1 !lpf_asr);

  cover property (cb $rose(mb_debug_sys_rst) ##1 lpf_exr ##1 (lpf_int0__0 && lpf_int));
  cover property (cb $fell(mb_debug_sys_rst) ##1 !lpf_exr ##1 (!lpf_int0__0 && !lpf_int));

  cover property (cb ##16 (Q == 1'b0)); // observe shift-to-zero convergence

endmodule

bind lpf_module lpf_module_sva sva_i (
  .slowest_sync_clk(slowest_sync_clk),
  .dcm_locked      (dcm_locked),
  .aux_reset_in    (aux_reset_in),
  .mb_debug_sys_rst(mb_debug_sys_rst),
  .ext_reset_in    (ext_reset_in),
  .lpf_int         (lpf_int),

  .asr_lpf         (asr_lpf),
  .lpf_asr         (lpf_asr),
  .lpf_exr         (lpf_exr),
  .Q               (Q),
  .lpf_int0__0     (lpf_int0__0),

  .asr_lpf_reg     (asr_lpf_reg),
  .lpf_asr_reg     (lpf_asr_reg),
  .lpf_exr_reg     (lpf_exr_reg),
  .Q_reg           (Q_reg),
  .lpf_int0__0_reg (lpf_int0__0_reg),
  .lpf_int_reg     (lpf_int_reg)
);