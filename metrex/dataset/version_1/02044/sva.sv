// SVA for ddr_ctrl_wrapper
// Quality-focused, concise checks and key coverage

module ddr_ctrl_wrapper_sva #(parameter ADDR_WIDTH = 25);
  localparam int LOCAL_ADR_WIDTH = ADDR_WIDTH-2;

  // Mirror DUT encodings
  localparam [3:0] WAIT_READY = 4'h0;
  localparam [3:0] IDLE       = 4'h1;
  localparam [3:0] WRITE      = 4'h2;
  localparam [3:0] READ       = 4'h3;

  function automatic [31:0] mask(input int w);
    mask = (32'h1 << w) - 1;
  endfunction

  default clocking cb @(posedge local_clk_i); endclocking
  default disable iff (!local_reset_n_i);

  // Simple mappings
  assert property (dat_o == local_rdata_i);
  assert property (local_be_o == sel_i);
  assert property (local_wdata_o == dat_i);
  assert property (rdy_o == local_ready_i);
  assert property (idle_o == (state == IDLE));
  assert property (local_burstbegin_o == (local_write_req_o || local_read_req_o));

  // Address generation/alignment
  assert property (we_i |-> local_address_o == adr_i[LOCAL_ADR_WIDTH+1:2]);
  assert property (!we_i |-> local_address_o == (adr_i[LOCAL_ADR_WIDTH+1:2] & ~mask(buf_width_i)));
  assert property (!we_i |-> (local_address_o & mask(buf_width_i)) == '0);

  // Handshake/req formation (pulse, qualified, mutual excl)
  assert property ($rose(local_write_req_o) |-> !$past(local_write_req_o));
  assert property ($rose(local_read_req_o)  |-> !$past(local_read_req_o));
  assert property (!(local_write_req_o && local_read_req_o));
  assert property ($rose(local_write_req_o) |-> $past(state==IDLE && acc_i && we_i && local_ready_i));
  assert property ($rose(local_read_req_o)  |-> $past(state==IDLE && acc_i && !we_i && local_ready_i));

  // Size programming on requests
  assert property ($rose(local_write_req_o) |=> local_size_o == 7'd1);
  assert property ($rose(local_read_req_o)  |=> local_size_o == (7'(1) << $past(buf_width_i)));

  // ACK behavior and gating
  assert property (ack_o |-> acc_i);
  assert property ( (ack_o && we_i)  == (acc_i && ack_w) );
  assert property ( (ack_o && !we_i) == (acc_i && local_rdata_valid_i) );
  assert property ($rose(ack_w) |-> !$past(ack_w)); // write ack pulse is single-cycle

  // State transitions
  assert property (state==WAIT_READY && !local_ready_i |=> state==WAIT_READY);
  assert property (state==WAIT_READY &&  local_ready_i |=> state==IDLE);
  assert property (state==IDLE && acc_i && local_ready_i && we_i  |=> state==WRITE);
  assert property (state==IDLE && acc_i && local_ready_i && !we_i |=> state==READ);
  assert property (state==WRITE |=> state==IDLE);

  // READ channel: address base and stride, count and exit
  // On read start, ADR is aligned base
  assert property ($rose(local_read_req_o) |=> adr_o == ($past(adr_i) & ~mask($past(buf_width_i)+2)));
  // During READ, on each valid beat:
  // - base (upper) bits unchanged
  // - low word index increments modulo burst length
  assert property (state==READ && local_rdata_valid_i |=> 
                   ((adr_o & ~mask($past(buf_width_i)+2)) == ($past(adr_o) & ~mask($past(buf_width_i)+2))) &&
                   (((adr_o>>2) & mask($past(buf_width_i))) == (($past(adr_o>>2)+1) & mask($past(buf_width_i)))) );

  // Count behavior and termination
  assert property (state==READ |-> count <= (32'(1) << buf_width_i));
  assert property (state==READ && local_rdata_valid_i |=> count == $past(count)+1);
  assert property (state==READ && count == (32'(1)<<buf_width_i) |=> state==IDLE && count==0);
  assert property (state==READ && count < (32'(1)<<buf_width_i) && !local_rdata_valid_i |=> state==READ);

  // Coverage
  cover property (state==IDLE && acc_i && we_i && local_ready_i ##1 local_write_req_o && ack_o && we_i);
  cover property (state==IDLE && acc_i && !we_i && local_ready_i ##1 local_read_req_o
                  ##1 (state==READ, local_rdata_valid_i)[*2] ##1 state==READ && local_rdata_valid_i ##1 state==IDLE);
endmodule

bind ddr_ctrl_wrapper ddr_ctrl_wrapper_sva #(.ADDR_WIDTH(ADDR_WIDTH)) u_ddr_ctrl_wrapper_sva();