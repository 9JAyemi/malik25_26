
module register_monitor (
  input  wire clk,
  input  wire reset_n,
  input  wire [31:0] MonDReg,
  input  wire enable,
  output reg  [31:0] monitored_value
);

  always @(posedge clk or negedge reset_n) begin
    if (reset_n == 1'b0) begin
      monitored_value <= 0;
    end else begin
      if (enable) begin
        monitored_value <= MonDReg;
      end
    end
  end

endmodule
module lab9_soc_nios2_qsys_0_jtag_debug_module_wrapper (
  // inputs:
  input  [31:0] MonDReg,
  input  [31:0] break_readreg,
  input         clk,
  input         dbrk_hit0_latch,
  input         dbrk_hit1_latch,
  input         dbrk_hit2_latch,
  input         dbrk_hit3_latch,
  input         debugack,
  input         monitor_error,
  input         monitor_ready,
  input         reset_n,
  input         resetlatch,
  input         tracemem_on,
  input  [35:0] tracemem_trcdata,
  input         tracemem_tw,
  input   [6:0] trc_im_addr,
  input         trc_on,
  input         trc_wrap,
  input         trigbrktype,
  input         trigger_state_1,

  // outputs:
  output [37:0] jdo,
  output        jrst_n,
  output        st_ready_test_idle,
  output        take_action_break_a,
  output        take_action_break_b,
  output        take_action_break_c,
  output        take_action_ocimem_a,
  output        take_action_ocimem_b,
  output        take_action_tracectrl,
  output        take_action_tracemem_a,
  output        take_action_tracemem_b,
  output        take_no_action_break_a,
  output        take_no_action_break_b,
  output        take_no_action_break_c,
  output        take_no_action_ocimem_a,
  output        take_no_action_tracemem_a
);

  wire         vji_cdr;
  wire   [1:0] vji_ir_in;
  wire   [1:0] vji_ir_out;
  wire         vji_rti;
  wire         vji_sdr;
  wire         vji_tck;
  wire         vji_tdi;
  wire         vji_tdo;
  wire         vji_udr;
  wire         vji_uir;

  register_monitor monitor (
    .clk             (clk),
    .reset_n         (reset_n),
    .MonDReg         (MonDReg),
    .enable          (1'b1),
    .monitored_value (jdo[31:0])
  );

  assign jdo[37] = 1'b0;
  assign jdo[36] = 1'b0;
  assign jdo[35] = 1'b0;
  assign jdo[34] = 1'b0;
  assign jdo[33] = 1'b0;
  assign jdo[32] = 1'b0;

  assign jrst_n = 1'b0;
  assign st_ready_test_idle = 1'b0;
  assign take_action_break_a = 1'b0;
  assign take_action_break_b = 1'b0;
  assign take_action_break_c = 1'b0;
  assign take_action_ocimem_a = 1'b0;
  assign take_action_ocimem_b = 1'b0;
  assign take_action_tracectrl = 1'b0;
  assign take_action_tracemem_a = 1'b0;
  assign take_action_tracemem_b = 1'b0;
  assign take_no_action_break_a = 1'b1;
  assign take_no_action_break_b = 1'b1;
  assign take_no_action_break_c = 1'b1;
  assign take_no_action_ocimem_a = 1'b1;
  assign take_no_action_tracemem_a = 1'b1;
endmodule