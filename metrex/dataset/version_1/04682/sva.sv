// SVA checker for data_buffer
module data_buffer_sva #(
  parameter DEPTH = 8,
  parameter L = 3,
  parameter dat_width = 8
)(
  input  logic                   CLK,
  input  logic                   Rst,
  input  logic                   Wren,
  input  logic                   Rden,
  input  logic [L-1:0]           adr_wr_i,
  input  logic [L-1:0]           adr_rd_i,
  input  logic [dat_width-1:0]   Datain,
  input  logic [dat_width-1:0]   Dataout,
  input  logic                   Full,
  input  logic                   Empty,
  ref    logic [dat_width-1:0]   data_ram [0:DEPTH-1],
  ref    logic [L-1:0]           status_cnt
);

  default clocking cb @(posedge CLK); endclocking

  // Basic sanity/X checks
  assert property (cb !Rst |-> !$isunknown({Wren,Rden,adr_wr_i,adr_rd_i,Datain,Full,Empty,Dataout,status_cnt}));

  // Reset behavior
  assert property (cb Rst |-> (status_cnt==0 && Dataout==0 && !Full && Empty));

  // Range and flags
  assert property (cb status_cnt <= DEPTH);
  assert property (cb Full  == (status_cnt==DEPTH));
  assert property (cb Empty == (status_cnt==0));
  assert property (cb !(Full && Empty));

  // Count update rules (based on previous cycle inputs)
  assert property (cb disable iff (Rst)
                   $past(Wren) && !$past(Rden) && ($past(status_cnt) < DEPTH)
                   |-> status_cnt == $past(status_cnt)+1);

  assert property (cb disable iff (Rst)
                   $past(Rden) && ($past(status_cnt) > 0)
                   |-> status_cnt == $past(status_cnt)-1);

  assert property (cb disable iff (Rst)
                   !$past(Wren) && !$past(Rden)
                   |-> status_cnt == $past(status_cnt));

  assert property (cb disable iff (Rst)
                   $past(Wren) && !$past(Rden) && ($past(status_cnt) == DEPTH)
                   |-> status_cnt == DEPTH);

  assert property (cb disable iff (Rst)
                   $past(Wren) && $past(Rden) && ($past(status_cnt) == 0)
                   |-> status_cnt == 0);

  // Address use must be in range when used
  assert property (cb disable iff (Rst) $past(Wren) |-> ($past(adr_wr_i) < DEPTH));
  assert property (cb disable iff (Rst) $past(Rden) && ($past(status_cnt)>0) |-> ($past(adr_rd_i) < DEPTH));

  // Memory write effect (NB write visible next cycle)
  assert property (cb disable iff (Rst)
                   $past(Wren) |-> data_ram[$past(adr_wr_i)] == $past(Datain));

  // Dataout update/hold
  assert property (cb disable iff (Rst)
                   $past(Rden) && ($past(status_cnt)>0)
                   |-> Dataout == $past(data_ram[$past(adr_rd_i)]));

  assert property (cb disable iff (Rst)
                   !$past(Rden) |-> Dataout == $past(Dataout));

  // Read on empty: no change
  assert property (cb disable iff (Rst)
                   $past(Rden) && ($past(status_cnt)==0)
                   |-> (status_cnt==0 && Dataout==$past(Dataout)));

  // Coverage: fill to full
  cover property (cb disable iff (Rst)
                  status_cnt==0 ##1 (Wren && !Rden)[*DEPTH] ##1 status_cnt==DEPTH);

  // Coverage: drain to empty
  cover property (cb disable iff (Rst)
                  status_cnt==DEPTH ##1 (Rden && !Wren)[*DEPTH] ##1 status_cnt==0);

  // Coverage: simultaneous R/W in middle range
  cover property (cb disable iff (Rst)
                  (status_cnt inside {[1:DEPTH-1]}) ##1 (Wren && Rden) ##1 status_cnt == $past(status_cnt)-1);

  // Coverage: write when full (no read)
  cover property (cb disable iff (Rst)
                  status_cnt==DEPTH ##1 (Wren && !Rden) ##1 status_cnt==DEPTH);

  // Coverage: read when empty (ignored)
  cover property (cb disable iff (Rst)
                  status_cnt==0 ##1 Rden ##1 status_cnt==0);

  // Coverage: same-cycle same-address R/W
  cover property (cb disable iff (Rst)
                  (status_cnt>0) && (Wren && Rden && (adr_wr_i==adr_rd_i)));

endmodule

// Bind into DUT
bind data_buffer
  data_buffer_sva #(.DEPTH(DEPTH), .L(L), .dat_width(dat_width)) data_buffer_sva_i (
    .CLK(CLK),
    .Rst(Rst),
    .Wren(Wren),
    .Rden(Rden),
    .adr_wr_i(adr_wr_i),
    .adr_rd_i(adr_rd_i),
    .Datain(Datain),
    .Dataout(Dataout),
    .Full(Full),
    .Empty(Empty),
    .data_ram(data_ram),
    .status_cnt(status_cnt)
  );