// SVA checker for eth_rcr_unpack
module eth_rcr_unpack_sva #(parameter unpack_dst_addr = 48'hAABBCCDDEEFF) (
  input  logic        i_axi_rx_clk,
  input  logic        i_axi_rx_rst_n,
  input  logic        i_rx_axis_fifo_tvalid,
  input  logic [7:0]  i_rx_axis_fifo_tdata,
  input  logic        i_rx_axis_fifo_tlast,
  input  logic        i_axi_rx_data_tready,
  input  logic        o_rx_axis_fifo_tready,
  input  logic        o_axi_rx_clk,
  input  logic        o_axi_rx_rst_n,
  input  logic [7:0]  o_axi_rx_tdata,
  input  logic        o_axi_rx_data_tvalid,
  input  logic        o_axi_rx_data_tlast,
  input  logic        loop_back,
  // internal
  input  logic        state,
  input  logic [3:0]  pkt_len_cntr,
  input  logic        no_filter,
  input  logic [7:0]  dest_addr0,
  input  logic [7:0]  dest_addr1,
  input  logic [7:0]  dest_addr2,
  input  logic [7:0]  dest_addr3,
  input  logic [7:0]  dest_addr4,
  input  logic [7:0]  dest_addr5,
  input  logic [47:0] destination_addr
);
  localparam logic IDLE   = 1'b0;
  localparam logic STREAM = 1'b1;

  default clocking cb @(posedge i_axi_rx_clk); endclocking
  default disable iff (!i_axi_rx_rst_n);

  // Simple wiring assertions
  assert property (o_axi_rx_clk   == i_axi_rx_clk);
  assert property (o_axi_rx_rst_n == i_axi_rx_rst_n);
  assert property (o_rx_axis_fifo_tready == i_axi_rx_data_tready);

  // Reset values while reset is asserted (override default disable)
  assert property (@(posedge i_axi_rx_clk)
                   disable iff (1'b0)
                   (!i_axi_rx_rst_n |-> (o_axi_rx_data_tvalid==1'b0
                                       && state==IDLE
                                       && pkt_len_cntr==4'd0
                                       && o_axi_rx_tdata==8'd0
                                       && no_filter==1'b0
                                       && dest_addr0==8'd0 && dest_addr1==8'd0 && dest_addr2==8'd0
                                       && dest_addr3==8'd0 && dest_addr4==8'd0 && dest_addr5==8'd0)));
  // After reset release, tlast cleared in first IDLE cycle
  assert property ($rose(i_axi_rx_rst_n) |=> o_axi_rx_data_tlast==1'b0);

  // IDLE outputs deasserted
  assert property (state==IDLE |-> (o_axi_rx_data_tvalid==1'b0 && o_axi_rx_data_tlast==1'b0));

  // Destination address concatenation is consistent
  assert property (destination_addr == {dest_addr0,dest_addr1,dest_addr2,dest_addr3,dest_addr4,dest_addr5});

  // Header count behavior in IDLE
  sequence rx_hs; i_rx_axis_fifo_tvalid && i_axi_rx_data_tready; endsequence
  assert property (state==IDLE && rx_hs |=> ( ($past(pkt_len_cntr)!=4'd13) ? (pkt_len_cntr==$past(pkt_len_cntr)+1) : (pkt_len_cntr==4'd0) ));
  assert property (state==IDLE && !rx_hs |=> pkt_len_cntr==$past(pkt_len_cntr));

  // Capture of destination MAC bytes
  assert property (state==IDLE && rx_hs |=> 
                   (($past(pkt_len_cntr)==4'd0) -> (dest_addr0==$past(i_rx_axis_fifo_tdata))) &&
                   (($past(pkt_len_cntr)==4'd1) -> (dest_addr1==$past(i_rx_axis_fifo_tdata))) &&
                   (($past(pkt_len_cntr)==4'd2) -> (dest_addr2==$past(i_rx_axis_fifo_tdata))) &&
                   (($past(pkt_len_cntr)==4'd3) -> (dest_addr3==$past(i_rx_axis_fifo_tdata))) &&
                   (($past(pkt_len_cntr)==4'd4) -> (dest_addr4==$past(i_rx_axis_fifo_tdata))) &&
                   (($past(pkt_len_cntr)==4'd5) -> (dest_addr5==$past(i_rx_axis_fifo_tdata))));

  // Transition to STREAM after 14th byte, and correct filter decision
  assert property (state==IDLE && rx_hs && (pkt_len_cntr==4'd13)
                   |=> (state==STREAM && pkt_len_cntr==4'd0
                        && no_filter == ($past(loop_back) || ((!$past(loop_back)) && ($past(destination_addr)==unpack_dst_addr)))));

  // STREAM behavior: outputs mirror/gated inputs
  assert property (state==STREAM |-> (o_axi_rx_tdata==i_rx_axis_fifo_tdata));
  assert property (state==STREAM |-> (o_axi_rx_data_tvalid == (i_rx_axis_fifo_tvalid && no_filter)));
  assert property (state==STREAM |-> (o_axi_rx_data_tlast  == (i_rx_axis_fifo_tlast  && no_filter)));

  // Return to IDLE on input TLAST
  assert property (state==STREAM && i_rx_axis_fifo_tlast |=> state==IDLE);

  // Counter behavior in STREAM
  assert property (state==STREAM |-> pkt_len_cntr==4'd0);

  // Stability while dropping
  assert property (state==STREAM && !no_filter |-> (o_axi_rx_data_tvalid==1'b0 && o_axi_rx_data_tlast==1'b0));

  // Header fields and filter stable during STREAM
  assert property (state==STREAM |-> $stable({dest_addr0,dest_addr1,dest_addr2,dest_addr3,dest_addr4,dest_addr5,destination_addr,no_filter}));

  // AXIS input stability assumption under backpressure
  assume property (i_rx_axis_fifo_tvalid && !i_axi_rx_data_tready |=> $stable({i_rx_axis_fifo_tdata,i_rx_axis_fifo_tlast}));
  // Output stability under backpressure (follows from design + assumption)
  assert property (o_axi_rx_data_tvalid && !i_axi_rx_data_tready |=> $stable({o_axi_rx_tdata,o_axi_rx_data_tlast}));

  // Coverage
  // Enter STREAM due to address match (non-loopback)
  cover property ( (state==STREAM && $past(state==IDLE))
                   && $past(rx_hs && pkt_len_cntr==4'd13)
                   && $past(!loop_back) && $past(destination_addr==unpack_dst_addr)
                   && no_filter );

  // Enter STREAM due to loop_back
  cover property ( (state==STREAM && $past(state==IDLE))
                   && $past(rx_hs && pkt_len_cntr==4'd13)
                   && $past(loop_back)
                   && no_filter );

  // Enter STREAM with drop (address mismatch)
  cover property ( (state==STREAM && $past(state==IDLE))
                   && $past(rx_hs && pkt_len_cntr==4'd13)
                   && $past(!loop_back) && $past(destination_addr!=unpack_dst_addr)
                   && !no_filter );

  // STREAM terminates on TLAST
  cover property (state==STREAM && i_rx_axis_fifo_tlast ##1 state==IDLE);

  // Backpressure during header accumulate
  cover property (state==IDLE && i_rx_axis_fifo_tvalid && !i_axi_rx_data_tready);
endmodule

// Bind the checker to the DUT
bind eth_rcr_unpack eth_rcr_unpack_sva #(.unpack_dst_addr(unpack_dst_addr)) i_eth_rcr_unpack_sva (
  .i_axi_rx_clk(i_axi_rx_clk),
  .i_axi_rx_rst_n(i_axi_rx_rst_n),
  .i_rx_axis_fifo_tvalid(i_rx_axis_fifo_tvalid),
  .i_rx_axis_fifo_tdata(i_rx_axis_fifo_tdata),
  .i_rx_axis_fifo_tlast(i_rx_axis_fifo_tlast),
  .i_axi_rx_data_tready(i_axi_rx_data_tready),
  .o_rx_axis_fifo_tready(o_rx_axis_fifo_tready),
  .o_axi_rx_clk(o_axi_rx_clk),
  .o_axi_rx_rst_n(o_axi_rx_rst_n),
  .o_axi_rx_tdata(o_axi_rx_tdata),
  .o_axi_rx_data_tvalid(o_axi_rx_data_tvalid),
  .o_axi_rx_data_tlast(o_axi_rx_data_tlast),
  .loop_back(loop_back),
  .state(state),
  .pkt_len_cntr(pkt_len_cntr),
  .no_filter(no_filter),
  .dest_addr0(dest_addr[0]),
  .dest_addr1(dest_addr[1]),
  .dest_addr2(dest_addr[2]),
  .dest_addr3(dest_addr[3]),
  .dest_addr4(dest_addr[4]),
  .dest_addr5(dest_addr[5]),
  .destination_addr(destination_addr)
);