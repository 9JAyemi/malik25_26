// SVA checker for fifo_generator_rx_inst_blk_mem_gen_prim_wrapper__parameterized0
// Bind this checker to the DUT instance.

module fifo_rx_sva #(
  parameter int DEPTH = 16,
  parameter int PTR_W = 4
)(
  input logic                  clk,
  input logic [8:0]            din,
  input logic [8:0]            dout,
  input logic [11:0]           Q,
  input logic [11:0]           count_d1_reg,
  input logic                  ram_full_fb_i_reg,
  input logic                  tmp_ram_rd_en,

  // internal DUT state
  input logic [PTR_W-1:0]      write_ptr,
  input logic [PTR_W-1:0]      read_ptr,
  input logic [PTR_W-1:0]      count,
  input logic [11:0]           count_reg
);

  default clocking cb @(posedge clk); endclocking

  // Recreate DUT gating
  logic empty_h, full_h, rd_h, wr_h;
  assign empty_h = (count == '0);
  // Note: this matches DUT's bug (full when count==16, which is unreachable with 4-bit count)
  assign full_h  = (count == DEPTH[PTR_W-1:0]); 
  assign rd_h    = (tmp_ram_rd_en && !empty_h);
  assign wr_h    = (!full_h);

  // Basic invariants
  assert property (Q == count_reg) else $error("Q must mirror count_reg");

  // count_reg mux timing (nonblocking semantics)
  assert property (count_reg == ($past(ram_full_fb_i_reg) ? $past(count_d1_reg) : $past(count)))
    else $error("count_reg mux/update incorrect");

  // Pointer updates
  assert property (wr_h |-> write_ptr == $past(write_ptr) + 1)
    else $error("write_ptr must increment on write");
  assert property (rd_h |-> read_ptr == $past(read_ptr) + 1)
    else $error("read_ptr must increment on read");
  assert property ((!wr_h && !rd_h) |-> $stable(write_ptr) && $stable(read_ptr))
    else $error("Pointers changed without corresponding enable");

  // Count behavior (golden: cnt' = cnt + wr - rd)
  assert property ((!wr_h && !rd_h) |-> count == $past(count))
    else $error("Count changed without rd/wr");
  assert property (( wr_h && !rd_h) |-> count == $past(count) + 1)
    else $error("Count did not increment on write");
  assert property ((!wr_h &&  rd_h) |-> count == $past(count) - 1)
    else $error("Count did not decrement on read");
  assert property (( wr_h &&  rd_h) |-> count == $past(count))
    else $error("Count must hold on simultaneous read+write");

  // Bounds / safety
  assert property (count <= (DEPTH-1))
    else $error("Count overflow");
  assert property (!(tmp_ram_rd_en && empty_h))
    else $error("Read attempted on empty FIFO");
  assert property (!((count != '0) && wr_h && !rd_h && (write_ptr == read_ptr)))
    else $error("Overwrite of unread data (write_ptr == read_ptr while not empty)");

  // dout stability: if read_ptr stable and we didn't write the addressed entry last cycle, dout should be stable
  assert property ( ($stable(read_ptr) && !($past(wr_h) && ($past(write_ptr) == read_ptr))) |-> $stable(dout) )
    else $error("dout changed without read_ptr change or write to that entry");

  // Coverage
  cover property (count == '0);
  cover property (count == (DEPTH-1));
  cover property ($past(write_ptr) == {PTR_W{1'b1}} && wr_h && write_ptr == '0); // write_ptr wrap
  cover property ($past(read_ptr)  == {PTR_W{1'b1}} && rd_h && read_ptr  == '0); // read_ptr wrap
  cover property (wr_h && rd_h);                         // simultaneous rd/wr
  cover property ($rose(ram_full_fb_i_reg));             // exercise count_reg mux alt path
  cover property ($fell(ram_full_fb_i_reg));
  cover property (!wr_h);                                // attempt to deassert wr_h (exposes unreachable 'full' bug)
endmodule

bind fifo_generator_rx_inst_blk_mem_gen_prim_wrapper__parameterized0
  fifo_rx_sva #(.DEPTH(16), .PTR_W(4))
  fifo_rx_sva_i (
    .clk(clk),
    .din(din),
    .dout(dout),
    .Q(Q),
    .count_d1_reg(count_d1_reg),
    .ram_full_fb_i_reg(ram_full_fb_i_reg),
    .tmp_ram_rd_en(tmp_ram_rd_en),
    .write_ptr(write_ptr),
    .read_ptr(read_ptr),
    .count(count),
    .count_reg(count_reg)
  );