// SVA for sd_card
// Bind this checker: bind sd_card sd_card_sva sva();

module sd_card_sva (sd_card dut);

  // Basic invariants
  // io_sdhc/io_conf/io_lba mapping
  assert property (@(posedge dut.sd_sck) dut.io_sdhc == (dut.allow_sdhc && dut.conf[0]));
  assert property (@(posedge dut.sd_sck) dut.io_conf == (dut.csd_wptr == 6'd0));
  assert property (@(posedge dut.sd_sck)
                   dut.io_sdhc ? (dut.io_lba == dut.lba)
                               : (dut.io_lba == {9'd0, dut.lba[31:9]}));

  // Handshakes: io_rd/io_wr never overlap; ack drops both; ack must not be high while rd/wr asserted
  assert property (@(posedge dut.sd_sck) !(dut.io_rd && dut.io_wr));
  assert property (@(posedge dut.io_ack) !dut.io_rd && !dut.io_wr);
  assert property (@(posedge dut.sd_sck) dut.io_rd |-> !dut.io_ack);
  assert property (@(posedge dut.sd_sck) dut.io_wr |-> !dut.io_ack);

  // sd_sck bit/byte counters
  assert property (@(posedge dut.sd_cs) dut.bit_cnt == 3'd0);
  assert property (@(posedge dut.sd_sck)
                   (dut.sd_cs==0 && $past(dut.sd_cs==0) && $past(dut.bit_cnt)!=3'd7)
                   |-> dut.bit_cnt == $past(dut.bit_cnt)+3'd1);
  assert property (@(posedge dut.sd_sck)
                   (dut.sd_cs==0 && $past(dut.sd_cs==0) && $past(dut.bit_cnt)==3'd7)
                   |-> dut.bit_cnt == 3'd0);

  // New command only when both FSMs idle; byte_cnt reset
  assert property (@(posedge dut.sd_sck)
                   $rose(dut.new_cmd_rcvd)
                   |-> (dut.read_state==dut.RD_STATE_IDLE && dut.write_state==dut.WR_STATE_IDLE && dut.byte_cnt==4'd0));

  // Buffer pointers reset on new command
  assert property (@(posedge dut.new_cmd_rcvd) dut.buffer_wptr==9'd0 && dut.buffer_rptr==9'd0);

  // Ack synchronizers only active in their wait modes
  assert property (@(posedge dut.sd_sck) (dut.write_state!=dut.WR_STATE_BUSY) |-> !dut.wr_io_ack);
  assert property (@(posedge dut.sd_sck) (dut.read_state ==dut.RD_STATE_IDLE) |-> !dut.rd_io_ack);

  // READ path (CMD17=0x51, CSD=0x49, CID=0x4a)
  // Launch CMD17 -> WAIT_IO and request IO read
  assert property (@(negedge dut.sd_sck)
                   (dut.sd_cs==0 && dut.cmd==8'h51 && dut.byte_cnt==(5+dut.NCR) && dut.bit_cnt==3'd7)
                   |-> (dut.read_state==dut.RD_STATE_WAIT_IO && dut.req_io_rd));
  // WAIT_IO -> SEND_TOKEN on rd_io_ack at end-of-byte
  assert property (@(negedge dut.sd_sck)
                   (dut.read_state==dut.RD_STATE_WAIT_IO && dut.rd_io_ack && dut.bit_cnt==3'd7)
                   |-> dut.read_state==dut.RD_STATE_SEND_TOKEN);
  // Token value
  assert property (@(negedge dut.sd_sck)
                   (dut.read_state==dut.RD_STATE_SEND_TOKEN)
                   |-> (dut.sd_sdo == dut.READ_DATA_TOKEN[~dut.bit_cnt]));
  // SEND_TOKEN -> SEND_DATA on byte boundary
  assert property (@(negedge dut.sd_sck)
                   (dut.read_state==dut.RD_STATE_SEND_TOKEN && dut.bit_cnt==3'd7)
                   |-> dut.read_state==dut.RD_STATE_SEND_DATA);
  // Data source mapping
  assert property (@(negedge dut.sd_sck)
                   (dut.read_state==dut.RD_STATE_SEND_DATA && dut.cmd==8'h51)
                   |-> (dut.sd_sdo == dut.buffer_dout[~dut.bit_cnt]));
  assert property (@(negedge dut.sd_sck)
                   (dut.read_state==dut.RD_STATE_SEND_DATA && dut.cmd==8'h49)
                   |-> (dut.sd_sdo == dut.csd_byte[~dut.bit_cnt]));
  assert property (@(negedge dut.sd_sck)
                   (dut.read_state==dut.RD_STATE_SEND_DATA && dut.cmd==8'h4a)
                   |-> (dut.sd_sdo == dut.cid_byte[~dut.bit_cnt]));
  // Exit conditions
  assert property (@(negedge dut.sd_sck)
                   (dut.read_state==dut.RD_STATE_SEND_DATA && dut.cmd==8'h51 && dut.bit_cnt==3'd7 && dut.buffer_read_sector_done)
                   |-> dut.read_state==dut.RD_STATE_IDLE);
  assert property (@(negedge dut.sd_sck)
                   (dut.read_state==dut.RD_STATE_SEND_DATA && (dut.cmd==8'h49||dut.cmd==8'h4a) && dut.bit_cnt==3'd7 && dut.buffer_read_ciscid_done)
                   |-> dut.read_state==dut.RD_STATE_IDLE);
  // Buffer read strobe only during token/data send
  assert property (@(negedge dut.sd_sck)
                   dut.buffer_read_strobe |-> (dut.read_state==dut.RD_STATE_SEND_TOKEN || dut.read_state==dut.RD_STATE_SEND_DATA));

  // WRITE path (CMD24=0x58)
  // First write state implies CMD24
  assert property (@(posedge dut.sd_sck) $rose(dut.write_state==dut.WR_STATE_EXP_DTOKEN) |-> dut.cmd==8'h58);
  // Data token (0xFE) to start RECV_DATA at end-of-byte
  assert property (@(posedge dut.sd_sck)
                   (dut.write_state==dut.WR_STATE_EXP_DTOKEN && dut.bit_cnt==3'd7 && {dut.sbuf,dut.sd_sdi}==8'hfe)
                   |-> dut.write_state==dut.WR_STATE_RECV_DATA);
  // Buffer write strobe only in RECV_DATA; pointer increments
  assert property (@(posedge dut.sd_sck) dut.buffer_write_strobe |-> dut.write_state==dut.WR_STATE_RECV_DATA);
  assert property (@(posedge dut.sd_sck)
                   (dut.write_state==dut.WR_STATE_RECV_DATA && dut.buffer_write_strobe)
                   |-> dut.buffer_wptr == $past(dut.buffer_wptr)+9'd1);
  // RECV_DATA completes at 512 bytes
  assert property (@(posedge dut.sd_sck)
                   (dut.write_state==dut.WR_STATE_RECV_DATA && dut.buffer_wptr==9'd511)
                   |-> dut.write_state==dut.WR_STATE_RECV_CRC0);
  // CRC pipeline and data response -> BUSY with IO write request
  assert property (@(posedge dut.sd_sck)
                   (dut.write_state==dut.WR_STATE_RECV_CRC0) |-> dut.write_state==dut.WR_STATE_RECV_CRC1);
  assert property (@(posedge dut.sd_sck)
                   (dut.write_state==dut.WR_STATE_RECV_CRC1) |-> dut.write_state==dut.WR_STATE_SEND_DRESP);
  assert property (@(posedge dut.sd_sck)
                   (dut.write_state==dut.WR_STATE_SEND_DRESP) |-> (dut.req_io_wr && dut.write_state==dut.WR_STATE_BUSY));
  // BUSY holds sd_sdo low; exit on wr_io_ack
  assert property (@(negedge dut.sd_sck) (dut.write_state==dut.WR_STATE_BUSY) |-> (dut.sd_sdo==1'b0));
  assert property (@(posedge dut.sd_sck)
                   (dut.write_state==dut.WR_STATE_BUSY && dut.wr_io_ack)
                   |-> dut.write_state==dut.WR_STATE_IDLE);
  // Data response token value
  assert property (@(negedge dut.sd_sck)
                   (dut.write_state==dut.WR_STATE_SEND_DRESP)
                   |-> (dut.sd_sdo == dut.WRITE_DATA_RESPONSE[~dut.bit_cnt]));
  // No illegal write state
  assert property (@(posedge dut.sd_sck) !dut.illegal_write_state);

  // Coverage: key command flows and modes
  cover property (@(posedge dut.sd_sck)
                  $rose(dut.new_cmd_rcvd) && dut.cmd==8'h51
                  ##[1:200] dut.read_state==dut.RD_STATE_WAIT_IO
                  ##[1:200] dut.read_state==dut.RD_STATE_SEND_TOKEN
                  ##[1:200] dut.read_state==dut.RD_STATE_SEND_DATA
                  ##[1:2000] dut.read_state==dut.RD_STATE_IDLE);

  cover property (@(posedge dut.sd_sck)
                  $rose(dut.new_cmd_rcvd) && dut.cmd==8'h58
                  ##[1:200] dut.write_state==dut.WR_STATE_EXP_DTOKEN
                  ##[1:200] dut.write_state==dut.WR_STATE_RECV_DATA
                  ##[1:200] dut.write_state==dut.WR_STATE_RECV_CRC0
                  ##1       dut.write_state==dut.WR_STATE_RECV_CRC1
                  ##1       dut.write_state==dut.WR_STATE_SEND_DRESP
                  ##1       dut.write_state==dut.WR_STATE_BUSY
                  ##[1:200] dut.write_state==dut.WR_STATE_IDLE);

  cover property (@(posedge dut.sd_sck) $rose(dut.new_cmd_rcvd) && dut.cmd==8'h49);
  cover property (@(posedge dut.sd_sck) $rose(dut.new_cmd_rcvd) && dut.cmd==8'h4a);
  cover property (@(posedge dut.sd_sck) $rose(dut.new_cmd_rcvd) && dut.cmd==8'h7a);
  cover property (@(posedge dut.sd_sck) $rose(dut.new_cmd_rcvd) && dut.cmd==8'h77 ##[1:100] $rose(dut.new_cmd_rcvd) && dut.cmd==8'h69);
  cover property (@(posedge dut.sd_sck) dut.allow_sdhc && dut.conf[0] && dut.io_sdhc);

  // Handshake coverage
  cover property (@(posedge dut.sd_sck) $rose(dut.io_rd) ##[1:100] $rose(dut.io_ack) ##1 !dut.io_rd);
  cover property (@(posedge dut.sd_sck) $rose(dut.io_wr) ##[1:100] $rose(dut.io_ack) ##1 !dut.io_wr);

endmodule