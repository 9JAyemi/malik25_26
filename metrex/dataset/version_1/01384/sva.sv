// SVA for sram_byte_en: concise, high-quality checks and coverage
module sram_byte_en_sva #(
  parameter DATA_WIDTH    = 128,
  parameter ADDRESS_WIDTH = 7
)(
  input                           i_clk,
  input      [DATA_WIDTH-1:0]     i_write_data,
  input                           i_write_enable,
  input      [ADDRESS_WIDTH-1:0]  i_address,
  input      [DATA_WIDTH/8-1:0]   i_byte_enable,
  input      [DATA_WIDTH-1:0]     o_read_data
);

  localparam BYTES = DATA_WIDTH/8;

  // Simple shadow model of memory
  logic [DATA_WIDTH-1:0] exp_mem [0:(1<<ADDRESS_WIDTH)-1];

  // Update model on write, honoring byte enables
  always_ff @(posedge i_clk) begin
    if (i_write_enable) begin
      for (int j=0; j<BYTES; j++) begin
        if (i_byte_enable[j])
          exp_mem[i_address][j*8 +: 8] <= i_write_data[j*8 +: 8];
      end
    end
  end

  default clocking cb @(posedge i_clk); endclocking

  // Basic X checks on controls and enabled data lanes
  ap_ctrl_known: assert property (!$isunknown(i_write_enable) && !$isunknown(i_address));
  ap_be_known:   assert property (!$isunknown(i_byte_enable));
  generate
    genvar k;
    for (k=0; k<BYTES; k++) begin: g_lane_x
      ap_wdata_lane_known: assert property (i_write_enable && i_byte_enable[k] |-> !$isunknown(i_write_data[k*8 +: 8]));
    end
  endgenerate

  // Read-during-write returns zero
  ap_rdwr_zero: assert property (i_write_enable |-> ##0 (o_read_data == {DATA_WIDTH{1'b0}}));

  // Read returns model content when not writing
  ap_read_ok:   assert property (!i_write_enable |-> ##0 (o_read_data == exp_mem[i_address]));

  // Optional: addressed entry must not change when no write
  ap_no_spur_update: assert property (!i_write_enable |=> (exp_mem[$past(i_address)] == $past(exp_mem[$past(i_address)])));

  // Coverage
  //  - full write, zero-byte write, single-byte writes, partial writes, RAW (write then read same addr), back-to-back writes
  cp_full_write:   cover property (i_write_enable && (&i_byte_enable));
  cp_zero_be:      cover property (i_write_enable && (i_byte_enable == '0));
  generate
    for (k=0; k<BYTES; k++) begin: g_single_be_cov
      cp_single_byte: cover property (i_write_enable && (i_byte_enable == ({{(BYTES-1){1'b0}},1'b1} << k)));
    end
  endgenerate
  cp_partial_write: cover property (i_write_enable && ($countones(i_byte_enable) inside {[2:BYTES-1]}));

  cp_raw_same_addr: cover property (i_write_enable ##1 (!i_write_enable && (i_address == $past(i_address))));
  cp_b2b_wr_same:   cover property (i_write_enable ##1 (i_write_enable && (i_address == $past(i_address))));
  cp_b2b_wr_diff:   cover property (i_write_enable ##1 (i_write_enable && (i_address != $past(i_address))));

endmodule

// Bind into DUT
bind sram_byte_en sram_byte_en_sva #(.DATA_WIDTH(DATA_WIDTH), .ADDRESS_WIDTH(ADDRESS_WIDTH)) sva_i (
  .i_clk(i_clk),
  .i_write_data(i_write_data),
  .i_write_enable(i_write_enable),
  .i_address(i_address),
  .i_byte_enable(i_byte_enable),
  .o_read_data(o_read_data)
);