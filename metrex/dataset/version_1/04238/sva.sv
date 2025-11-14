// SVA for Ethernet_MAC (drop inside the module or bind to it). Focused, concise checks and coverage.

default clocking cb @(posedge clk); endclocking
default disable iff (reset)

// Reset values
assert property (reset |=> state==IDLE && frame_cnt==0 && tx_en==0 && rx_en==0);

// Enables (one-hot by state)
assert property (state==IDLE  |-> tx_en==0 && rx_en==1);
assert property (state!=IDLE  |-> tx_en==1 && rx_en==0);
assert property (!(tx_en && rx_en));

// IDLE behavior
assert property (state==IDLE && data_in==0 |=> state==IDLE);
assert property (state==IDLE && data_in!=0 |=> state==PREAMBLE && frame_cnt==0);
assert property (state==IDLE |-> $stable(data_out));
assert property (state==IDLE |-> dest_mac_out==dest_mac && src_mac_out==src_mac);
assert property (state!=IDLE |-> $stable(dest_mac_out) && $stable(src_mac_out));

// Frame counter resets on state change
assert property (state != $past(state) |-> frame_cnt==0);

// PREAMBLE
assert property (state==PREAMBLE && frame_cnt!=7  |=> state==PREAMBLE && frame_cnt==$past(frame_cnt)+1);
assert property (state==PREAMBLE && frame_cnt==7  |=> state==SFD && frame_cnt==0);
if (n>=8) begin
  assert property (state==PREAMBLE && frame_cnt!=7 |-> data_out[7:0]==8'h55);
end

// SFD (bit-by-bit as coded)
assert property (state==SFD && frame_cnt!=31 |=> state==SFD && frame_cnt==$past(frame_cnt)+1);
assert property (state==SFD && frame_cnt==31 |=> state==DEST_MAC && frame_cnt==0);
assert property (state==SFD && frame_cnt!=31 |-> data_out[0]==sfd[frame_cnt]);

// DEST_MAC (bit-by-bit as coded)
assert property (state==DEST_MAC && frame_cnt!=47 |=> state==DEST_MAC && frame_cnt==$past(frame_cnt)+1);
assert property (state==DEST_MAC && frame_cnt==47 |=> state==SRC_MAC && frame_cnt==0);
assert property (state==DEST_MAC && frame_cnt!=47 |-> data_out[0]==dest_mac_reg[frame_cnt]);

// SRC_MAC (length/flow only; content indexing in RTL is suspect)
assert property (state==SRC_MAC && frame_cnt!=95 |=> state==SRC_MAC && frame_cnt==$past(frame_cnt)+1);
assert property (state==SRC_MAC && frame_cnt==95 |=> state==LENGTH && frame_cnt==0);

// LENGTH (zeros as coded)
assert property (state==LENGTH && frame_cnt!=111 |=> state==LENGTH && frame_cnt==$past(frame_cnt)+1);
assert property (state==LENGTH && frame_cnt==111 |=> state==DATA && frame_cnt==0);
assert property (state==LENGTH && frame_cnt!=111 |-> data_out=='0);

// DATA (flow only; content indexing in RTL is suspect)
localparam int DATA_TERM = (n*8)-1;
assert property (state==DATA && frame_cnt!=DATA_TERM |=> state==DATA && frame_cnt==$past(frame_cnt)+1);
assert property (state==DATA && frame_cnt==DATA_TERM |=> state==FCS && frame_cnt==0);

// FCS (zeros as coded)
assert property (state==FCS && frame_cnt!=127 |=> state==FCS && frame_cnt==$past(frame_cnt)+1);
assert property (state==FCS && frame_cnt==127 |=> state==IDLE && frame_cnt==0);
assert property (state==FCS && frame_cnt!=127 |-> data_out=='0);

// Cross-state coverage (full frame)
cover property (
  state==IDLE && data_in!=0 ##1
  state==PREAMBLE ##[1:$]
  state==SFD      ##[1:$]
  state==DEST_MAC ##[1:$]
  state==SRC_MAC  ##[1:$]
  state==LENGTH   ##[1:$]
  state==DATA     ##[1:$]
  state==FCS      ##[1:$]
  state==IDLE
);

// Boundary/event coverage
cover property (state==PREAMBLE && frame_cnt==7 ##1 state==SFD && frame_cnt==0);
cover property (state==SFD      && frame_cnt==31 ##1 state==DEST_MAC && frame_cnt==0);
cover property (state==DEST_MAC && frame_cnt==47 ##1 state==SRC_MAC  && frame_cnt==0);
cover property (state==SRC_MAC  && frame_cnt==95 ##1 state==LENGTH   && frame_cnt==0);
cover property (state==LENGTH   && frame_cnt==111##1 state==DATA     && frame_cnt==0);
cover property (state==DATA     && frame_cnt==DATA_TERM ##1 state==FCS && frame_cnt==0);
cover property (state==FCS      && frame_cnt==127##1 state==IDLE     && frame_cnt==0);