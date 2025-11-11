// SVA checker for fifo_buffer
module fifo_buffer_sva #(
  parameter int ADDR_WIDTH = 1,
  parameter int DEPTH      = 2
)(
  input  logic                 clk,
  input  logic                 reset,

  input  logic                 if_empty_n,
  input  logic                 if_read_ce,
  input  logic                 if_read,
  input  logic [7:0]           if_dout,
  input  logic                 if_full_n,
  input  logic                 if_write_ce,
  input  logic                 if_write,
  input  logic [7:0]           if_din,

  // internal state
  input  logic [ADDR_WIDTH:0]  wr_ptr,
  input  logic [ADDR_WIDTH:0]  rd_ptr,
  input  logic [ADDR_WIDTH:0]  count
);

  // handshake qualifiers
  wire push          = if_write & if_write_ce & if_full_n;
  wire pop           = if_read  & if_read_ce  & if_empty_n;
  wire attempt_push  = if_write & if_write_ce;
  wire attempt_pop   = if_read  & if_read_ce;

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Reset state
  assert property (@cb reset |-> (wr_ptr==0 && rd_ptr==0 && count==0 && if_empty_n==0 && if_full_n==1));

  // Count bounds and flag consistency
  assert property (@cb (count <= DEPTH));
  assert property (@cb if_empty_n == (count > 0));
  assert property (@cb if_full_n  == (count < DEPTH));

  // Count update
  assert property (@cb $past(!reset) |-> count == $past(count) + $past(push) - $past(pop));

  // Blocked ops do not change state
  assert property (@cb $past(attempt_push && !if_full_n && !reset) |-> (wr_ptr == $past(wr_ptr) && count == $past(count)));
  assert property (@cb $past(attempt_pop  && !if_empty_n && !reset) |-> (rd_ptr == $past(rd_ptr) && count == $past(count)));

  // Pointer increments and wrap modulo DEPTH
  assert property (@cb $past(!reset && push) |-> wr_ptr == (($past(wr_ptr) == (DEPTH-1)) ? '0 : $past(wr_ptr)+1));
  assert property (@cb $past(!reset && !push) |-> wr_ptr == $past(wr_ptr));

  assert property (@cb $past(!reset && pop)  |-> rd_ptr == (($past(rd_ptr) == (DEPTH-1)) ? '0 : $past(rd_ptr)+1));
  assert property (@cb $past(!reset && !pop) |-> rd_ptr == $past(rd_ptr));

  // Memory index must be in range on actual accesses (prevent OOB)
  assert property (@cb $past(!reset && push) |-> $past(wr_ptr) < DEPTH);
  assert property (@cb $past(!reset && pop)  |-> $past(rd_ptr) < DEPTH);

  // Data integrity for writing into empty FIFO: first subsequent pop returns that data
  property p_empty_write_read_order;
    logic [7:0] d;
    @(posedge clk) disable iff (reset)
      (push && ($past(count)==0), d = $past(if_din))
      |-> (!pop)[*0:$] ##1 (pop && (if_dout == d));
  endproperty
  assert property (p_empty_write_read_order);

  // Useful coverage
  cover property (@cb (count==0) ##1 push [*DEPTH] ##1 (count==DEPTH));
  cover property (@cb (count==DEPTH) ##1 pop [*DEPTH] ##1 (count==0));
  cover property (@cb $past(push) && ($past(wr_ptr)==(DEPTH-1)) ##1 (wr_ptr==0));
  cover property (@cb $past(pop)  && ($past(rd_ptr)==(DEPTH-1)) ##1 (rd_ptr==0));
  cover property (@cb push && pop);
  cover property (@cb (count==DEPTH) && attempt_push);
  cover property (@cb (count==0)     && attempt_pop);

endmodule

// Bind into the DUT (connects to internals)
bind fifo_buffer fifo_buffer_sva #(.ADDR_WIDTH(ADDR_WIDTH), .DEPTH(DEPTH)) i_fifo_buffer_sva (
  .clk       (clk),
  .reset     (reset),
  .if_empty_n(if_empty_n),
  .if_read_ce(if_read_ce),
  .if_read   (if_read),
  .if_dout   (if_dout),
  .if_full_n (if_full_n),
  .if_write_ce(if_write_ce),
  .if_write  (if_write),
  .if_din    (if_din),
  .wr_ptr    (wr_ptr),
  .rd_ptr    (rd_ptr),
  .count     (count)
);