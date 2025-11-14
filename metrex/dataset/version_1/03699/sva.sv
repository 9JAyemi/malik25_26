// SVA checker for all RAM variants: synchronous read, write-first behavior is NOT implemented (read-first/old-data on same-cycle write)
module mem_sva #(parameter int DW=8, AW=4)
(
  input  logic                   clk,
  input  logic                   write_enable,
  input  logic [DW-1:0]          data_in,
  input  logic [AW-1:0]          address_in,
  input  logic [DW-1:0]          data_out
);
  localparam int DEPTH = (1<<AW);

  // Lightweight reference model (pre-update read capture)
  logic [DW-1:0] ref_mem [0:DEPTH-1];
  bit            valid   [0:DEPTH-1];
  logic [DW-1:0] pre_read_q;
  bit            pre_valid_q;

  always_ff @(posedge clk) begin
    pre_read_q  <= ref_mem[address_in];
    pre_valid_q <= valid[address_in];
    if (write_enable) begin
      ref_mem[address_in] <= data_in;
      valid[address_in]   <= 1'b1;
    end
  end

  // Basic sanity: no X/Z on inputs at sampling; output known when reading a known location
  a_no_x_inputs:        assert property (@(posedge clk) !$isunknown({write_enable, address_in, data_in}));
  a_no_x_out_when_valid:assert property (@(posedge clk) pre_valid_q |-> !$isunknown(data_out));

  // Synchronous read returns "old" memory value (read-first) for current address
  a_sync_read_old:      assert property (@(posedge clk) pre_valid_q |-> (data_out == pre_read_q));

  // New data becomes visible on the next cycle when address is held
  a_new_visible_next:   assert property (@(posedge clk)
                                         $past(write_enable) && ($past(address_in) == address_in)
                                         |-> (data_out == $past(data_in)));

  // Read-during-write (same-cycle) must return old data, not the just-written data
  a_rdwr_same_cycle_old:assert property (@(posedge clk)
                                         write_enable && pre_valid_q |-> (data_out == pre_read_q));

  // Coverage: write, read, hazard, extremes, data patterns
  c_write:              cover property (@(posedge clk) write_enable);
  c_read_valid:         cover property (@(posedge clk) pre_valid_q && !write_enable);
  c_rdwr_hazard:        cover property (@(posedge clk) write_enable && pre_valid_q);
  c_addr_min:           cover property (@(posedge clk) address_in == '0);
  c_addr_max:           cover property (@(posedge clk) address_in == (DEPTH-1));
  c_data_zeros:         cover property (@(posedge clk) write_enable && data_in == '0);
  c_data_ones:          cover property (@(posedge clk) write_enable && &data_in);
endmodule

// Bind the checker to all provided modules
bind block_ram                 mem_sva #(.DW(DATA_WIDTH), .AW(ADDRESS_WIDTH)) mem_sva_i (.*);
bind distributed_ram           mem_sva #(.DW(DATA_WIDTH), .AW(ADDRESS_WIDTH)) mem_sva_i (.*);
bind distributed_ram_manual    mem_sva #(.DW(DATA_WIDTH), .AW(ADDRESS_WIDTH)) mem_sva_i (.*);
bind distributed_ram_manual_syn mem_sva #(.DW(DATA_WIDTH), .AW(ADDRESS_WIDTH)) mem_sva_i (.*);