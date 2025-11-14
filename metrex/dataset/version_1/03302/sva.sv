// SVA for fifo_buffer
// Bind these assertions to the DUT. Focus: reset behavior, pointer/count updates,
// ready flags, sizing, overflow/underflow protection, and key corner cases.

module fifo_buffer_sva #(
  parameter DATA_WIDTH = 32,
  parameter FIFO_WIDTH = 8
)(
  input  logic                     rst,
  input  logic                     WR_CLK,

  // write side
  input  logic                     WR_RDY,
  input  logic                     WR_ACT,
  input  logic                     WR_STB,
  input  logic [DATA_WIDTH-1:0]    WR_DATA,
  input  logic                     WR_STARVED,

  // read side
  input  logic                     RD_STB,
  input  logic                     RD_RDY,
  input  logic                     RD_ACT,
  input  logic [DATA_WIDTH-1:0]    RD_DATA,
  input  logic                     RD_INACTIVE,

  input  logic [23:0]              WR_SIZE,
  input  logic [23:0]              RD_SIZE,

  // Internal state (bind to DUT regs)
  input  logic [FIFO_WIDTH-1:0]    wr_ptr,
  input  logic [FIFO_WIDTH-1:0]    rd_ptr,
  input  logic [FIFO_WIDTH-1:0]    count
);

  localparam int ADDR_WIDTH = FIFO_WIDTH;
  localparam int DEPTH      = (1 << ADDR_WIDTH);
  localparam int MASK       = DEPTH - 1;
  localparam logic [23:0] DEPTH24 = DEPTH[23:0];

  default clocking cb @(posedge WR_CLK); endclocking
  default disable iff (rst);

  // Shorthands
  let wr_fire = (WR_STB && WR_ACT && WR_RDY);
  let rd_fire = (RD_STB && RD_ACT && RD_RDY);

  // Reset state (one cycle after rst high)
  assert property (@(posedge WR_CLK) rst |=> (wr_ptr==0 && rd_ptr==0 && count==0 &&
                                              WR_RDY==1 && RD_RDY==0 &&
                                              RD_INACTIVE==1 && WR_STARVED==0 &&
                                              WR_SIZE==DEPTH24 && RD_SIZE==DEPTH24));

  // Output consistency
  assert property (RD_RDY == ~RD_INACTIVE);
  assert property (WR_RDY == ~WR_STARVED);

  // Pointer updates
  assert property (wr_fire |=> wr_ptr == $past(wr_ptr) + 1);
  assert property (!wr_fire |=> wr_ptr == $past(wr_ptr));

  assert property (rd_fire |=> rd_ptr == $past(rd_ptr) + 1);
  assert property (!rd_fire |=> rd_ptr == $past(rd_ptr));

  // Count updates (golden model for occupancy)
  assert property ( wr_fire && !rd_fire |=> count == $past(count) + 1 );
  assert property ( rd_fire && !wr_fire |=> count == $past(count) - 1 );
  // Simultaneous R/W must keep occupancy unchanged
  assert property ( wr_fire &&  rd_fire |=> count == $past(count) );

  // Count must be within 0..DEPTH-1
  assert property ( $unsigned(count) < DEPTH );

  // Count matches pointer distance modulo depth
  assert property ( $unsigned(count) == (($unsigned(wr_ptr) - $unsigned(rd_ptr)) & MASK) );

  // Ready flags vs occupancy
  assert property ( RD_RDY == ($unsigned(count) > 0) );
  assert property ( WR_RDY == ($unsigned(count) < DEPTH) );

  // Size outputs
  assert property ( WR_SIZE == DEPTH24 );
  assert property ( RD_SIZE == (DEPTH24 - $unsigned(count)) );

  // Interface safety: no accept when not ready
  assert property ( !(WR_STB && WR_ACT) or WR_RDY );
  assert property ( !(RD_STB && RD_ACT) or RD_RDY );

  // No X on key outputs
  assert property ( !$isunknown({WR_RDY,RD_RDY,WR_STARVED,RD_INACTIVE}) );
  assert property ( !$isunknown({WR_SIZE,RD_SIZE}) );

  // Liveness to full: writing from DEPTH-1 with no read should deassert WR_RDY
  assert property ( ($unsigned(count)==DEPTH-1) && wr_fire && !rd_fire |=> !WR_RDY );

  // Liveness to empty: reading from 1 with no write should deassert RD_RDY
  assert property ( ($unsigned(count)==1) && rd_fire && !wr_fire |=> !RD_RDY );

  // Coverage
  cover property ( rst ##1 !rst ##1 wr_fire ##[1:$] rd_fire );                 // reset->first write->first read
  cover property ( wr_fire && rd_fire );                                        // simultaneous read+write
  cover property ( $rose(wr_ptr==0) );                                          // write pointer wrap
  cover property ( $rose(rd_ptr==0) );                                          // read pointer wrap
  cover property ( ($unsigned(count)==DEPTH-1) ##1 wr_fire ##1 !WR_RDY );       // reach full and block write
  cover property ( ($unsigned(count)==1)       ##1 rd_fire ##1 !RD_RDY );       // reach empty and block read
  cover property ( RD_SIZE==0 );                                                 // empty size
  cover property ( RD_SIZE==DEPTH24 );                                           // max size

endmodule

// Example bind (explicitly connect internals)
bind fifo_buffer fifo_buffer_sva #(.DATA_WIDTH(DATA_WIDTH), .FIFO_WIDTH(FIFO_WIDTH)) u_sva (
  .rst(rst),
  .WR_CLK(WR_CLK),

  .WR_RDY(WR_RDY),
  .WR_ACT(WR_ACT),
  .WR_STB(WR_STB),
  .WR_DATA(WR_DATA),
  .WR_STARVED(WR_STARVED),

  .RD_STB(RD_STB),
  .RD_RDY(RD_RDY),
  .RD_ACT(RD_ACT),
  .RD_DATA(RD_DATA),
  .RD_INACTIVE(RD_INACTIVE),

  .WR_SIZE(WR_SIZE),
  .RD_SIZE(RD_SIZE),

  .wr_ptr(wr_ptr),
  .rd_ptr(rd_ptr),
  .count(count)
);