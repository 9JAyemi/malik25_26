// SVA for MM_slave
module MM_slave_sva (
  input  logic        clock_clk,
  input  logic        reset_reset,
  input  logic [7:0]  avs_s0_address,
  input  logic        avs_s0_read,
  input  logic        avs_s0_write,
  input  logic [31:0] avs_s0_writedata,
  input  logic [31:0] avs_s0_readdata,
  input  logic        avs_s0_waitrequest,
  input  logic        LED_OUT,

  // internal regs
  input  logic        Reg_Status_Read,
  input  logic        Reg_Status_Write,
  input  logic [31:0] data_in,
  input  logic [31:0] data_out
);

  default clocking cb @(posedge clock_clk); endclocking

  // Handshake helpers
  sequence s_write; !avs_s0_waitrequest && avs_s0_write; endsequence
  sequence s_read;  !avs_s0_waitrequest && avs_s0_read;  endsequence

  // Combinational outputs and waitrequest behavior
  assert property (avs_s0_readdata == 32'h0);
  assert property (!$isunknown(avs_s0_waitrequest) && !$isunknown(avs_s0_readdata));
  assert property (avs_s0_waitrequest == (Reg_Status_Read || Reg_Status_Write));
  assert property (avs_s0_waitrequest == 1'b0);

  // Status regs are never asserted
  assert property (Reg_Status_Read  == 1'b0);
  assert property (Reg_Status_Write == 1'b0);

  // Synchronous reset effects
  assert property (reset_reset |=> (data_in==32'h0 && data_out==32'h0 &&
                                    Reg_Status_Write==1'b0 && Reg_Status_Read==1'b0));

  // Write acceptance updates
  assert property (disable iff (reset_reset)
                   s_write |=> (data_in == $past(avs_s0_writedata) &&
                                LED_OUT == $past(avs_s0_writedata[0])));

  // No unintended updates
  assert property (disable iff (reset_reset) $changed(data_in)  |-> $past(s_write));
  assert property (disable iff (reset_reset) $changed(LED_OUT)  |-> ($past(s_write) &&
                                                                     LED_OUT == $past(avs_s0_writedata[0])));

  // data_out is constant zero in this RTL
  assert property (data_out == 32'h0);

  // Known LED after any write
  assert property (disable iff (reset_reset) s_write |=> !$isunknown(LED_OUT));

  // Coverage
  cover property (disable iff (reset_reset) s_write);
  cover property (disable iff (reset_reset) s_read);
  cover property (disable iff (reset_reset) (s_write and s_read));           // concurrent R/W
  cover property (disable iff (reset_reset) s_write ##1 s_write);            // back-to-back writes
  cover property (disable iff (reset_reset) s_write ##1 s_write ##1
                                  (LED_OUT != $past(LED_OUT)));              // LED toggles across writes

endmodule

bind MM_slave MM_slave_sva sva_MM_slave (.*);