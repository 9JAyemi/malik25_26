// SVA for fifo_memory
// Bind this file to the DUT; concise, high-signal-coverage checks.

module fifo_memory_sva #(
  parameter int DW       = 8,
  parameter int DEPTH    = 8,
  parameter int REG      = 0,
  parameter int AW       = $clog2(DEPTH),
  parameter int PROGFULL = DEPTH-1
)(
  input  logic                 clk,
  input  logic                 nreset,
  input  logic                 clear,
  input  logic [DW-1:0]        din,
  input  logic                 wr_en,
  output logic                 full,
  output logic                 almost_full,
  input  logic                 rd_en,
  output logic [DW-1:0]        dout,
  output logic                 empty,
  input  logic [AW-1:0]        rd_count,

  // tap internal state
  input  logic [AW-1:0]        wr_addr,
  input  logic [AW-1:0]        rd_addr,
  input  logic                 empty_reg
);

  // Recompute qualified enables and raw empty like DUT
  wire fifo_write = wr_en & ~full;
  wire fifo_read  = rd_en & ~empty;

  wire ptr_match       = (wr_addr == rd_addr);
  wire calc_fifo_empty = ptr_match & (wr_addr[AW-1] == rd_addr[AW-1]);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!nreset);

  // Reset/clear behavior
  assert property ( !nreset |-> (wr_addr==0 && rd_addr==0 && rd_count==0) );
  assert property ( clear   |-> (wr_addr==0 && rd_addr==0 && rd_count==0) );

  // Pointer movement
  assert property ( fifo_write |=> wr_addr == $past(wr_addr)+1 );
  assert property ( fifo_read  |=> rd_addr == $past(rd_addr)+1 );

  // Count updates
  assert property ( ( fifo_write &&  fifo_read) |=> rd_count == $past(rd_count) );
  assert property ( ( fifo_write && !fifo_read) |=> rd_count == $past(rd_count)+1 );
  assert property ( (!fifo_write &&  fifo_read) |=> rd_count == $past(rd_count)-1 );
  assert property ( (!fifo_write && !fifo_read) |=> rd_count == $past(rd_count) );

  // Count matches pointer distance modulo 2^AW
  assert property ( rd_count == (wr_addr - rd_addr) );

  // Flag correctness
  // almost_full is pure compare
  assert property ( almost_full == (rd_count == PROGFULL) );

  // empty pipelining matches REG parameter
  generate
    if (REG==0) begin
      assert property ( empty == calc_fifo_empty );
    end else begin
      assert property ( empty == $past(calc_fifo_empty) );
      // internal pipe correctness
      assert property ( empty_reg == calc_fifo_empty );
    end
  endgenerate

  // Safety: when almost full and a write-only happens, full should assert next cycle
  // (catches full-detection bugs)
  assert property ( (rd_count==PROGFULL && wr_en && !rd_en) |=> full );

  // Safety: no overwrite of unread entries (write to an address cannot recur before it is read)
  property p_no_overwrite;
    logic [AW-1:0] a;
    (fifo_write, a = wr_addr)
    |->
    (!(fifo_write && (wr_addr==a))) until_with (fifo_read && (rd_addr==a));
  endproperty
  assert property ( p_no_overwrite );

  // Sanity: outputs block illegal ops (redundant with definitions but good guards)
  assert property ( full  |-> !fifo_write );
  assert property ( empty |-> !fifo_read  );

  // Coverage
  cover property ( !nreset ##1 nreset );
  cover property ( fifo_write && !fifo_read );        // write-only
  cover property ( fifo_read  && !fifo_write );       // read-only
  cover property ( fifo_write &&  fifo_read );        // simultaneous
  cover property ( rd_count==PROGFULL );              // almost full reached
  cover property ( (rd_count==PROGFULL && wr_en && !rd_en) ##1 full ); // full after AF write
  cover property ( $past(wr_addr)=={AW{1'b1}} && fifo_write && wr_addr=={AW{1'b0}} ); // wrap

endmodule

// Bind to DUT (connects to internal regs via name)
bind fifo_memory fifo_memory_sva #(
  .DW(DW), .DEPTH(DEPTH), .REG(REG), .AW(AW), .PROGFULL(PROGFULL)
) u_fifo_memory_sva (.*);