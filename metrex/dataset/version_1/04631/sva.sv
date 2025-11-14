// SVA for fifo_64in_out_blk_mem_gen
// Bindable, concise, checks key functionality and provides targeted coverage.

module fifo_64in_out_blk_mem_gen_sva
(
  input logic              wr_clk,
  input logic              rd_clk,
  input logic              I1,
  input logic              tmp_ram_rd_en,
  input logic [63:0]       din,
  input logic [63:0]       dout,

  input logic [2:0]        read_address,
  input logic [2:0]        write_address,
  input logic [2:0]        num_entries,
  input logic [2:0]        next_write_address,
  input logic [2:0]        next_num_entries,

  input logic [7:0]        read_data,
  input logic [7:0]        write_data,
  input logic              write_enable,
  input logic              read_enable,

  input logic [7:0]        data [0:7]
);

  // Basic protocol: enables must reflect gating conditions in RTL
  assert property (@(posedge wr_clk) write_enable == (I1 && (num_entries != 8'b1000)));
  assert property (@(posedge rd_clk) read_enable  == (tmp_ram_rd_en && (num_entries != 8'b000)));

  // Address advance/stability
  assert property (@(posedge wr_clk) write_enable |=> write_address == $past(next_write_address));
  assert property (@(posedge wr_clk) !write_enable |=> $stable(write_address));

  assert property (@(posedge rd_clk) read_enable  |=> read_address  == $past(read_address) + 1);
  assert property (@(posedge rd_clk) !read_enable |=> $stable(read_address));

  // next_* consistency
  assert property (@(posedge wr_clk) next_write_address == write_address + 1);
  assert property (@(posedge wr_clk or posedge rd_clk)
                   next_num_entries ==
                     ((I1 && (num_entries != 8'b1000)) ? num_entries + 1 :
                      (tmp_ram_rd_en && (num_entries != 8'b000)) ? num_entries - 1 : num_entries));

  // Memory write on write_enable
  assert property (@(posedge wr_clk) write_enable |=> data[$past(write_address)] == $past(din[7:0]));

  // No underflow: if empty and read requested, read_enable must not assert
  assert property (@(posedge rd_clk) (tmp_ram_rd_en && (num_entries == 3'd0)) |-> !read_enable);

  // No overflow (intended spec): if full (7 entries for 8-deep) and write requested, must not write
  // This will flag the width bug (num_entries != 8'b1000) in the RTL.
  assert property (@(posedge wr_clk) (I1 && (num_entries == 3'd7)) |-> !write_enable);

  // Data path
  assert property (@(posedge rd_clk) dout == {56'h0, read_data});      // structural mapping
  assert property (@(posedge rd_clk) read_enable |=> dout[7:0] == $past(data[$past(read_address)]));
  assert property (@(posedge wr_clk or posedge rd_clk) dout[63:8] == 56'h0);

  // Sanity: no X on enables when requested
  assert property (@(posedge wr_clk) I1 |-> !$isunknown(write_enable));
  assert property (@(posedge rd_clk) tmp_ram_rd_en |-> !$isunknown(read_enable));

  // Coverage: writes, reads, wraps, empty/full visits
  cover property (@(posedge wr_clk) write_enable);
  cover property (@(posedge rd_clk) read_enable);
  cover property (@(posedge wr_clk) (write_address == 3'd7 && write_enable) ##1 (write_address == 3'd0));
  cover property (@(posedge rd_clk)  (read_address  == 3'd7 && read_enable)  ##1 (read_address  == 3'd0));
  cover property (@(posedge wr_clk) num_entries == 3'd7);
  cover property (@(posedge rd_clk) num_entries == 3'd0);

endmodule

// Bind into the DUT (connects internal regs/arrays)
bind fifo_64in_out_blk_mem_gen fifo_64in_out_blk_mem_gen_sva
(
  .wr_clk(wr_clk),
  .rd_clk(rd_clk),
  .I1(I1),
  .tmp_ram_rd_en(tmp_ram_rd_en),
  .din(din),
  .dout(dout),

  .read_address(read_address),
  .write_address(write_address),
  .num_entries(num_entries),
  .next_write_address(next_write_address),
  .next_num_entries(next_num_entries),

  .read_data(read_data),
  .write_data(write_data),
  .write_enable(write_enable),
  .read_enable(read_enable),

  .data(data)
);