// SVA for mdio_master
// Bind this module into mdio_master for internal signal visibility.
`ifndef MDIO_MASTER_SVA
`define MDIO_MASTER_SVA

bind mdio_master mdio_master_sva mdio_master_sva_i();

module mdio_master_sva;

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Helper
  wire bit_advance = (count_reg == 0 && !cycle_reg);

  // Reset defaults
  assert property (rst |-> state_reg==STATE_IDLE && count_reg==0 && bit_count_reg==0 &&
                           cycle_reg==0 && cmd_ready==0 && data_out_valid==0 &&
                           mdc_o==0 && mdio_t==1 && busy==0);

  // Ready/valid protocol on command
  assert property (cmd_ready |-> state_reg==STATE_IDLE && !data_out_valid);
  assert property (state_reg!=STATE_IDLE |-> !cmd_ready);
  // Load on handshake
  assert property ((state_reg==STATE_IDLE && cmd_ready && cmd_valid)
                   |=> state_reg==STATE_PREAMBLE &&
                       op_reg==$past(cmd_opcode) &&
                       data_reg=={2'b01,$past(cmd_opcode),$past(cmd_phy_addr),$past(cmd_reg_addr),2'b10,$past(cmd_data)} &&
                       mdio_t==0 && mdio_o==1 && bit_count_reg==6'd32);

  // Preamble behavior
  assert property (state_reg==STATE_PREAMBLE |-> mdio_t==0 && mdio_o==1);
  assert property (state_reg==STATE_PREAMBLE && bit_advance && bit_count_reg>6'd1
                   |=> state_reg==STATE_PREAMBLE && bit_count_reg==$past(bit_count_reg)-1);
  assert property (state_reg==STATE_PREAMBLE && bit_advance && bit_count_reg==6'd1
                   |=> state_reg==STATE_TRANSFER && bit_count_reg==6'd32);

  // MDC generation constraints
  assert property (count_reg>0 |=> $stable(mdc_o));
  assert property ($rose(mdc_o) |-> $past(count_reg)==0 && $past(cycle_reg)==1);
  assert property ($fell(mdc_o) |-> $past(count_reg)==0 && $past(cycle_reg)==0);

  // Transfer shifting and bit count
  assert property (state_reg==STATE_TRANSFER && bit_advance && bit_count_reg>6'd1
                   |=> bit_count_reg==$past(bit_count_reg)-1 &&
                       data_reg=={$past(data_reg[30:0]), $past(mdio_i_reg)});

  // Turnaround and MDIO tristate control
  // For reads, release MDIO at bit_count==19 and keep released thereafter
  assert property (state_reg==STATE_TRANSFER && bit_advance &&
                   (op_reg inside {2'b10,2'b11}) && bit_count_reg==6'd19
                   |=> mdio_t==1);
  assert property ((state_reg==STATE_TRANSFER && (op_reg inside {2'b10,2'b11}) && mdio_t==0)
                   |-> bit_count_reg>6'd19);
  // For writes, keep driving during transfer until last bit
  assert property (state_reg==STATE_TRANSFER && !(op_reg inside {2'b10,2'b11}) && bit_count_reg>6'd1
                   |-> mdio_t==0);

  // End of transfer and IDLE return
  assert property (state_reg==STATE_TRANSFER && bit_advance && bit_count_reg==6'd1
                   |=> state_reg==STATE_IDLE && mdio_t==1);

  // Read data return protocol
  assert property ($rose(data_out_valid)
                   |-> $past(state_reg==STATE_TRANSFER && bit_advance && bit_count_reg==6'd1) &&
                       ($past(op_reg) inside {2'b10,2'b11}));
  assert property (state_reg==STATE_TRANSFER && bit_advance && bit_count_reg==6'd1 &&
                   (op_reg inside {2'b10,2'b11})
                   |=> data_out_valid && data_out==$past(data_reg)[15:0]);

  // Read data valid sticky until ready and data stability
  assert property (data_out_valid && !data_out_ready |=> data_out_valid && $stable(data_out));
  // Do not accept new cmd while read data pending
  assert property (data_out_valid && !data_out_ready |-> !cmd_ready);

  // Busy behavior: only zero when fully quiescent and no new cmd taken
  assert property ((state_reg==STATE_IDLE && count_reg==0 && !cycle_reg && mdc_o==0 &&
                    !(cmd_ready && cmd_valid)) |-> !busy);
  assert property ((state_reg!=STATE_IDLE || count_reg!=0 || cycle_reg || mdc_o) |-> busy);

  // ------------- Coverage -------------
  // Basic write transaction
  cover property (state_reg==STATE_IDLE && cmd_ready && cmd_valid && !(cmd_opcode inside {2'b10,2'b11})
                  ##1 state_reg==STATE_PREAMBLE
                  ##[1:$] state_reg==STATE_TRANSFER
                  ##[1:$] state_reg==STATE_IDLE && !busy);

  // Read transaction opcode 2'b10 with data return and handshake out
  cover property (state_reg==STATE_IDLE && cmd_ready && cmd_valid && cmd_opcode==2'b10
                  ##[1:$] $rose(data_out_valid)
                  ##[1:$] data_out_valid && data_out_ready ##1 !data_out_valid);

  // Read transaction opcode 2'b11 with turnaround observed
  cover property (state_reg==STATE_IDLE && cmd_ready && cmd_valid && cmd_opcode==2'b11
                  ##[1:$] (state_reg==STATE_TRANSFER && bit_advance && bit_count_reg==6'd19 && mdio_t==1)
                  ##[1:$] $rose(data_out_valid));

  // Prescale==0 corner with MDC activity
  cover property (state_reg==STATE_IDLE && cmd_ready && cmd_valid && prescale==8'd0
                  ##[1:$] $rose(mdc_o));

  // Busy deasserts after work completes
  cover property ($fell(busy));

endmodule
`endif