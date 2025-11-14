// SVA bind module for ibex_load_store_unit
// Focused, high-quality checks and coverage

bind ibex_load_store_unit ibex_load_store_unit_sva ();

module ibex_load_store_unit_sva;

  // Default clocking/reset
  default clocking cb @(posedge clk_i); endclocking
  default disable iff (!rst_ni);

  // Helpers
  function automatic [3:0] be_exp (input logic [1:0] typ, input logic [1:0] off, input logic handle);
    unique case (typ)
      2'b00: be_exp = handle
                      ? (off==2'b00 ? 4'b0000 :
                         off==2'b01 ? 4'b0001 :
                         off==2'b10 ? 4'b0011 :
                                      4'b0111)
                      : (off==2'b00 ? 4'b1111 :
                         off==2'b01 ? 4'b1110 :
                         off==2'b10 ? 4'b1100 :
                                      4'b1000);
      2'b01: be_exp = handle ? 4'b0001
                             : (off==2'b00 ? 4'b0011 :
                                off==2'b01 ? 4'b0110 :
                                off==2'b10 ? 4'b1100 :
                                             4'b1000);
      default: be_exp = (off==2'b00 ? 4'b0001 :
                         off==2'b01 ? 4'b0010 :
                         off==2'b10 ? 4'b0100 :
                                      4'b1000);
    endcase
  endfunction

  function automatic [31:0] wdata_rot (input logic [31:0] wd, input logic [1:0] off);
    unique case (off)
      2'b00: wdata_rot = wd;
      2'b01: wdata_rot = {wd[23:0], wd[31:24]};
      2'b10: wdata_rot = {wd[15:0], wd[31:16]};
      default: wdata_rot = {wd[7:0],  wd[31:8]};
    endcase
  endfunction

  // Reset values
  assert property (!rst_ni |=> (ls_fsm_cs==IDLE && !handle_misaligned_q && !pmp_err_q && !lsu_err_q));

  // FSM valid encoding
  assert property (ls_fsm_cs inside {IDLE, WAIT_GNT_MIS, WAIT_RVALID_MIS, WAIT_GNT, WAIT_RVALID, WAIT_RVALID_DONE});

  // Busy definition
  assert property (busy_o == (ls_fsm_cs != IDLE));

  // Address alignment and pass-throughs
  assert property (data_addr_o == {data_addr[31:2], 2'b00});
  assert property (data_addr_o[1:0] == 2'b00);
  assert property (data_we_o == data_we_ex_i);

  // Byte-enable and write-data formation
  assert property (data_be_o == be_exp(data_type_ex_i, data_addr[1:0], handle_misaligned_q));
  assert property (data_wdata_o == wdata_rot(data_wdata_ex_i, data_addr[1:0]));

  // split_misaligned_access logic
  assert property (split_misaligned_access ==
                   (((data_type_ex_i==2'b00) && (data_addr[1:0]!=2'b00)) ||
                    ((data_type_ex_i==2'b01) && (data_addr[1:0]==2'b11))));

  // Handshake outputs per state
  assert property (data_req_o ==
                   ((ls_fsm_cs==IDLE && data_req_ex_i) ||
                    (ls_fsm_cs==WAIT_GNT_MIS) ||
                    (ls_fsm_cs==WAIT_RVALID_MIS) ||
                    (ls_fsm_cs==WAIT_GNT)));

  // Address increment request behavior
  assert property ((ls_fsm_cs==WAIT_RVALID_MIS || ls_fsm_cs==WAIT_RVALID_DONE) |-> addr_incr_req_o);
  assert property ((ls_fsm_cs==WAIT_GNT) |-> (addr_incr_req_o==handle_misaligned_q));
  assert property ((ls_fsm_cs inside {IDLE, WAIT_RVALID, WAIT_GNT_MIS}) |-> !addr_incr_req_o);

  // Data valid only when completion (or PMP err) in WAIT_RVALID
  assert property (data_valid_o |-> (ls_fsm_cs==WAIT_RVALID && (data_rvalid_i || pmp_err_q)));
  assert property ((ls_fsm_cs==WAIT_RVALID && (data_rvalid_i || pmp_err_q)) |-> data_valid_o);

  // Error outputs well-formed and mutually exclusive
  assert property (!(load_err_o && store_err_o));
  assert property ((load_err_o || store_err_o) |-> (ls_fsm_cs==WAIT_RVALID));
  assert property (load_err_o  |-> !data_we_q);
  assert property (store_err_o |->  data_we_q);

  // Capture behaviors
  assert property (ctrl_update |=> (rdata_offset_q==$past(data_addr[1:0]) &&
                                    data_type_q     ==$past(data_type_ex_i) &&
                                    data_sign_ext_q ==$past(data_sign_ext_ex_i) &&
                                    data_we_q       ==$past(data_we_ex_i)));

  assert property (addr_update |=> (addr_last_q == $past(data_addr)));
  assert property (rdata_update |=> (rdata_q == $past(data_rdata_i[31:8])));

  // Key FSM transitions
  assert property ((ls_fsm_cs==IDLE && data_req_ex_i && data_gnt_i && !split_misaligned_access)
                   |=> (ls_fsm_cs==WAIT_RVALID && handle_misaligned_q==$past(split_misaligned_access)));

  assert property ((ls_fsm_cs==IDLE && data_req_ex_i && data_gnt_i &&  split_misaligned_access)
                   |=> (ls_fsm_cs==WAIT_RVALID_MIS && handle_misaligned_q==$past(split_misaligned_access)));

  assert property ((ls_fsm_cs==IDLE && data_req_ex_i && !data_gnt_i && !split_misaligned_access)
                   |=> (ls_fsm_cs==WAIT_GNT));

  assert property ((ls_fsm_cs==IDLE && data_req_ex_i && !data_gnt_i &&  split_misaligned_access)
                   |=> (ls_fsm_cs==WAIT_GNT_MIS));

  assert property ($past(ls_fsm_cs==WAIT_RVALID_MIS && (data_rvalid_i || pmp_err_q) &&  data_gnt_i) |=> ls_fsm_cs==WAIT_RVALID);
  assert property ($past(ls_fsm_cs==WAIT_RVALID_MIS && (data_rvalid_i || pmp_err_q) && !data_gnt_i) |=> ls_fsm_cs==WAIT_GNT);
  assert property ($past(ls_fsm_cs==WAIT_RVALID_MIS && !data_rvalid_i && !pmp_err_q && data_gnt_i) |=> ls_fsm_cs==WAIT_RVALID_DONE);

  assert property ($past(ls_fsm_cs==WAIT_GNT && (data_gnt_i || pmp_err_q)) |=> ls_fsm_cs==WAIT_RVALID);
  assert property ($past(ls_fsm_cs==WAIT_RVALID && (data_rvalid_i || pmp_err_q)) |=> (ls_fsm_cs==IDLE && !handle_misaligned_q));
  assert property ($past(ls_fsm_cs==WAIT_RVALID_DONE && data_rvalid_i) |=> ls_fsm_cs==WAIT_RVALID);

  // Lightweight coverage
  cover property (ls_fsm_cs==WAIT_GNT);
  cover property (ls_fsm_cs==WAIT_GNT_MIS);
  cover property (ls_fsm_cs==WAIT_RVALID_MIS);
  cover property (ls_fsm_cs==WAIT_RVALID_DONE);
  cover property (ls_fsm_cs==WAIT_RVALID && (data_rvalid_i || pmp_err_q) && data_valid_o);

  cover property (ls_fsm_cs==IDLE && data_req_ex_i && split_misaligned_access ##1
                  ls_fsm_cs==WAIT_RVALID_MIS ##[1:10] data_gnt_i && !data_rvalid_i ##1
                  ls_fsm_cs==WAIT_RVALID_DONE ##[1:10] data_rvalid_i ##1
                  ls_fsm_cs==WAIT_RVALID && data_valid_o);

  cover property (ls_fsm_cs==WAIT_RVALID && (data_rvalid_i || pmp_err_q) && load_err_o);
  cover property (ls_fsm_cs==WAIT_RVALID && (data_rvalid_i || pmp_err_q) && store_err_o);

  cover property (data_type_ex_i==2'b00 && data_addr[1:0]==2'b01 && data_be_o==4'b1110);
  cover property (data_type_ex_i==2'b01 && data_addr[1:0]==2'b10 && data_be_o==4'b1100);
  cover property (data_type_ex_i==2'b10 && data_addr[1:0]==2'b11 && data_be_o==4'b1000);

endmodule