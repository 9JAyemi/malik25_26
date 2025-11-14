// SVA checker for fifo_empty_block
module fifo_empty_block_sva #(parameter AW=2)
(
  input  logic                rd_clk,
  input  logic                reset,
  input  logic                rd_read,
  input  logic [AW:0]         rd_wr_gray_pointer,

  // DUT observable (incl. a few internals via bind)
  input  logic [AW:0]         rd_binary_pointer,
  input  logic [AW:0]         rd_gray_pointer,
  input  logic [AW-1:0]       rd_addr,
  input  logic                rd_fifo_empty,
  input  logic                rd_fifo_empty_next
);

  function automatic logic [AW:0] gray(input logic [AW:0] bin);
    return ({1'b0, bin[AW:1]} ^ bin);
  endfunction

  default clocking cb @(posedge rd_clk); endclocking

  // Async reset behavior (checked at clock edge while reset asserted)
  a_reset_state: assert property (@(posedge rd_clk)
    reset |-> (rd_binary_pointer=='0 && rd_gray_pointer=='0 && rd_fifo_empty==1'b1));

  // Disable rest during reset
  default disable iff (reset);

  // Structural mapping/invariants
  a_addr_map:        assert property (rd_addr == rd_binary_pointer[AW-1:0]);
  a_gray_invariant:  assert property (rd_gray_pointer == gray(rd_binary_pointer));
  a_no_x:            assert property (!$isunknown({rd_fifo_empty, rd_addr, rd_gray_pointer, rd_binary_pointer}));

  // Pointer behavior
  a_hold_no_read:    assert property (!rd_read |=> $stable(rd_binary_pointer) && $stable(rd_gray_pointer) && $stable(rd_addr));
  a_inc_on_read:     assert property ( rd_read |=> rd_binary_pointer == $past(rd_binary_pointer)+1 );
  a_addr_inc_read:   assert property ( rd_read |=> rd_addr == $past(rd_addr)+1 );
  a_gray_1bit_step:  assert property ( rd_read |=> $onehot(rd_gray_pointer ^ $past(rd_gray_pointer)) );

  // Empty flag correctness
  a_empty_pipeline:  assert property ( rd_fifo_empty == $past(rd_fifo_empty_next) );

  // Explicit empty semantics for read/no-read cases
  a_empty_no_read:   assert property ( !rd_read |-> ##1 rd_fifo_empty == (rd_gray_pointer == rd_wr_gray_pointer) );
  a_empty_on_read:   assert property (  rd_read |-> ##1 rd_fifo_empty == (gray(rd_binary_pointer+1) == rd_wr_gray_pointer) );

  // Coverage
  c_three_reads:     cover  property ( rd_read[*3] );
  c_wrap:            cover  property ( rd_read && (rd_binary_pointer[AW-1:0]=={AW{1'b1}}) ##1 rd_read && $rose(rd_binary_pointer[AW]) );
  c_empty_toggle0:   cover  property ( rd_fifo_empty ##1 !rd_fifo_empty );
  c_empty_toggle1:   cover  property ( !rd_fifo_empty ##1 rd_fifo_empty );
  c_empty_on_eq:     cover  property ( rd_read && (rd_gray_pointer==rd_wr_gray_pointer) ##1 rd_fifo_empty );

endmodule

// Bind into DUT (captures internal regs/wires for stronger checking)
bind fifo_empty_block fifo_empty_block_sva #(.AW(AW)) fifo_empty_block_sva_i
(
  .rd_clk(rd_clk),
  .reset(reset),
  .rd_read(rd_read),
  .rd_wr_gray_pointer(rd_wr_gray_pointer),

  .rd_binary_pointer(rd_binary_pointer),
  .rd_gray_pointer(rd_gray_pointer),
  .rd_addr(rd_addr),
  .rd_fifo_empty(rd_fifo_empty),
  .rd_fifo_empty_next(rd_fifo_empty_next)
);