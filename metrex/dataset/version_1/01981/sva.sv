// SVA for fifo_empty_block
module fifo_empty_block_sva #(parameter AW=2) (
  input              rd_clk,
  input              reset,
  input              rd_read,
  input  [AW:0]      rd_wr_gray_pointer,
  input              rd_fifo_empty,
  input  [AW-1:0]    rd_addr,
  input  [AW:0]      rd_gray_pointer,
  input  [AW:0]      rd_binary_pointer
);
  function automatic [AW:0] gray_enc(input [AW:0] b);
    gray_enc = {1'b0, b[AW:1]} ^ b;
  endfunction

  default clocking cb @(posedge rd_clk); endclocking

  // Reset state
  a_reset_state: assert property (reset |-> (rd_binary_pointer=='0 && rd_gray_pointer=='0 && rd_fifo_empty));

  // Binary pointer update (+rd_read) when not in or coming from reset
  a_bin_update: assert property (!reset && !$past(reset) |-> rd_binary_pointer == $past(rd_binary_pointer) + $past(rd_read));

  // Gray encoding invariant
  a_gray_invariant: assert property (!reset |-> rd_gray_pointer == gray_enc(rd_binary_pointer));

  // Gray changes by at most one bit per cycle
  a_gray_onebit: assert property (!reset && !$past(reset) |-> $onehot0(rd_gray_pointer ^ $past(rd_gray_pointer)));

  // Address mirrors low bits of binary pointer
  a_addr_match: assert property (rd_addr == rd_binary_pointer[AW-1:0]);

  // Empty flag = (current rd_gray_pointer == previous wr_gray_pointer)
  a_empty_def: assert property (!reset && !$past(reset) |-> rd_fifo_empty == (rd_gray_pointer == $past(rd_wr_gray_pointer)));

  // No X on key outputs after reset release
  a_no_x: assert property (!reset |-> !$isunknown({rd_fifo_empty, rd_addr, rd_gray_pointer}));

  // Coverage
  c_reset_release: cover property (reset ##1 !reset);
  c_read_pulse:    cover property (!reset && $rose(rd_read));
  c_empty_rose:    cover property (!reset && $rose(rd_fifo_empty));
  c_empty_fell:    cover property (!reset && $fell(rd_fifo_empty));
  c_wrap:          cover property (!reset && !$past(reset) &&
                                   $past(rd_read) &&
                                   $past(rd_binary_pointer) == { (AW+1){1'b1} });
endmodule

// Bind into DUT (connect internal rd_binary_pointer)
bind fifo_empty_block fifo_empty_block_sva #(.AW(AW)) fifo_empty_block_sva_i (
  .rd_clk(rd_clk),
  .reset(reset),
  .rd_read(rd_read),
  .rd_wr_gray_pointer(rd_wr_gray_pointer),
  .rd_fifo_empty(rd_fifo_empty),
  .rd_addr(rd_addr),
  .rd_gray_pointer(rd_gray_pointer),
  .rd_binary_pointer(rd_binary_pointer)
);