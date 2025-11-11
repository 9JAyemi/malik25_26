// SVA for credit_manager
// Bind this checker to the DUT. Concise, high-signal-coverage, with key safety and functional checks.

module credit_manager_sva #(
  parameter int MAX_PKTS = 0
)(
  input                     clk,
  input                     rst,

  // DUT IO
  input        [2:0]        o_fc_sel,
  input                     i_rcb_sel,
  input        [7:0]        i_fc_cplh,
  input        [11:0]       i_fc_cpld,
  input                     o_ready,
  input        [9:0]        i_dword_req_count,
  input                     i_cmt_stb,
  input        [9:0]        i_dword_rcv_count,
  input                     i_rcv_stb,

  // DUT internals (bound hierarchically)
  input        [7:0]        r_hdr_in_flt,
  input        [11:0]       r_dat_in_flt,
  input        [7:0]        r_max_hdr_req,
  input        [7:0]        r_hdr_rcv_size,
  input        [11:0]       w_data_credit_req_size,
  input        [11:0]       w_data_credit_rcv_size,
  input        [7:0]        w_hdr_avail,
  input        [11:0]       w_dat_avail,
  input        [15:0]       w_dword_avail,
  input                     w_hdr_rdy,
  input                     w_dat_rdy,
  input                     r_delay_rcv_stb
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Reset values
  assert property (rst |=> (r_hdr_in_flt==0 && r_dat_in_flt==0 && r_delay_rcv_stb==0));

  // Static outputs
  assert property (o_fc_sel == 3'h0);

  // Comb definitions/invariants
  assert property (w_hdr_avail == (i_fc_cplh - r_hdr_in_flt));
  assert property (w_dat_avail == (i_fc_cpld - r_dat_in_flt));
  assert property (w_dword_avail == {w_dat_avail,2'b00});
  assert property (w_hdr_rdy == (w_hdr_avail > r_max_hdr_req));
  assert property (w_dat_rdy == (w_dat_avail > w_data_credit_req_size));

  // Ready equation (parameterized)
  generate
    if (MAX_PKTS==0) begin
      assert property (o_ready == (w_hdr_rdy && w_dat_rdy));
    end else begin
      assert property (o_ready == ((w_hdr_rdy && w_dat_rdy) && ((r_hdr_in_flt>>3) <= MAX_PKTS)));
    end
  endgenerate

  // RCB-dependent header size calculation (requests)
  assert property ( i_rcb_sel && (i_dword_req_count < 32)  |-> r_max_hdr_req == 8'd1 );
  assert property ( i_rcb_sel && (i_dword_req_count >= 32) |-> r_max_hdr_req == i_dword_req_count[9:5] );
  assert property (!i_rcb_sel && (i_dword_req_count < 16)  |-> r_max_hdr_req == 8'd1 );
  assert property (!i_rcb_sel && (i_dword_req_count >= 16) |-> r_max_hdr_req == i_dword_req_count[9:4] );

  // RCB-dependent header size calculation (receives)
  assert property ( i_rcb_sel && (i_dword_rcv_count < 32)  |-> r_hdr_rcv_size == 8'd1 );
  assert property ( i_rcb_sel && (i_dword_rcv_count >= 32) |-> r_hdr_rcv_size == i_dword_rcv_count[9:5] );
  assert property (!i_rcb_sel && (i_dword_rcv_count < 16)  |-> r_hdr_rcv_size == 8'd1 );
  assert property (!i_rcb_sel && (i_dword_rcv_count >= 16) |-> r_hdr_rcv_size == i_dword_rcv_count[9:4] );

  // Data credit granularity (min 1 DW-aligned)
  assert property ( (i_dword_req_count[9:2]==0) |-> (w_data_credit_req_size==12'd1) );
  assert property ( (i_dword_req_count[9:2]!=0) |-> (w_data_credit_req_size=={4'd0,i_dword_req_count[9:2]}) );
  assert property ( (i_dword_rcv_count[9:2]==0) |-> (w_data_credit_rcv_size==12'd1) );
  assert property ( (i_dword_rcv_count[9:2]!=0) |-> (w_data_credit_rcv_size=={4'd0,i_dword_rcv_count[9:2]}) );

  // Handshake discipline: commit only when ready (prevents overflow)
  assert property (i_cmt_stb |-> o_ready);

  // Counter updates: add path on commit
  assert property ( i_cmt_stb |=> r_hdr_in_flt == $past(r_hdr_in_flt) + $past(r_max_hdr_req) );
  assert property ( i_cmt_stb |=> r_dat_in_flt == $past(r_dat_in_flt) + $past(w_data_credit_req_size) );

  // Delay flag behavior on simultaneous commit+receive
  assert property ( (i_cmt_stb && i_rcv_stb) |=> r_delay_rcv_stb );
  assert property ( (i_cmt_stb && !i_rcv_stb) |=> r_delay_rcv_stb == $past(r_delay_rcv_stb) );

  // Receive (or delayed receive) path: subtract once and clear delay
  assert property ( (!i_cmt_stb && (i_rcv_stb || r_delay_rcv_stb))
                    |-> (r_hdr_in_flt >= r_hdr_rcv_size) && (r_dat_in_flt >= w_data_credit_rcv_size) );
  assert property ( (!i_cmt_stb && (i_rcv_stb || r_delay_rcv_stb))
                    |=> (r_hdr_in_flt == $past(r_hdr_in_flt) - $past(r_hdr_rcv_size)) &&
                         (r_dat_in_flt == $past(r_dat_in_flt) - $past(w_data_credit_rcv_size)) &&
                         (r_delay_rcv_stb == 1'b0) );

  // Hold state when no activity
  assert property ( (!i_cmt_stb && !(i_rcv_stb || r_delay_rcv_stb))
                    |=> (r_hdr_in_flt==$past(r_hdr_in_flt)) &&
                        (r_dat_in_flt==$past(r_dat_in_flt)) &&
                        (r_delay_rcv_stb==$past(r_delay_rcv_stb)) );

  // While a delayed receive is pending under continuous commits, require stable receive sizes
  assert property ( r_delay_rcv_stb && i_cmt_stb |-> $stable(r_hdr_rcv_size) && $stable(w_data_credit_rcv_size) );

  // Coverage

  // Ready toggles
  cover property ($rose(o_ready));
  cover property ($fell(o_ready));

  // Commit-only, Receive-only, and Simultaneous commit+receive (delay)
  cover property (o_ready && i_cmt_stb && !i_rcv_stb);
  cover property (!i_cmt_stb && i_rcv_stb);
  cover property (i_cmt_stb && i_rcv_stb);
  cover property (!i_cmt_stb && r_delay_rcv_stb); // delayed consume

  // RCB mode and thresholds hit both sides
  cover property ( i_rcb_sel && (i_dword_req_count==10'd31) && (r_max_hdr_req==8'd1) );
  cover property ( i_rcb_sel && (i_dword_req_count==10'd32) && (r_max_hdr_req==8'd1) );
  cover property (!i_rcb_sel && (i_dword_req_count==10'd15) && (r_max_hdr_req==8'd1) );
  cover property (!i_rcb_sel && (i_dword_req_count==10'd16) && (r_max_hdr_req==8'd1) );
  cover property ( i_rcb_sel && (i_dword_req_count>=10'd64) && (r_max_hdr_req>8'd1) );
  cover property (!i_rcb_sel && (i_dword_req_count>=10'd32) && (r_max_hdr_req>8'd1) );

  // MAX_PKTS gating coverage (only when enabled)
  generate if (MAX_PKTS!=0) begin
    cover property ( (w_hdr_rdy && w_dat_rdy) && ((r_hdr_in_flt>>3) >  MAX_PKTS) && !o_ready );
    cover property ( (w_hdr_rdy && w_dat_rdy) && ((r_hdr_in_flt>>3) <= MAX_PKTS) &&  o_ready );
  end endgenerate

endmodule

// Bind to all instances of credit_manager
bind credit_manager credit_manager_sva #(.MAX_PKTS(MAX_PKTS)) cm_sva (
  .clk, .rst,
  .o_fc_sel, .i_rcb_sel, .i_fc_cplh, .i_fc_cpld, .o_ready,
  .i_dword_req_count, .i_cmt_stb, .i_dword_rcv_count, .i_rcv_stb,
  .r_hdr_in_flt, .r_dat_in_flt, .r_max_hdr_req, .r_hdr_rcv_size,
  .w_data_credit_req_size, .w_data_credit_rcv_size,
  .w_hdr_avail, .w_dat_avail, .w_dword_avail, .w_hdr_rdy, .w_dat_rdy,
  .r_delay_rcv_stb
);