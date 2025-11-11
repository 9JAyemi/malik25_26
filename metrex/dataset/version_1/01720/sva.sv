// SVA for generic_sram_line_en
// Bind this module to the DUT instance.

module generic_sram_line_en_sva #(
  parameter DATA_WIDTH         = 128,
  parameter ADDRESS_WIDTH      = 7,
  parameter INITIALIZE_TO_ZERO = 0
)(
  input                           i_clk,
  input      [DATA_WIDTH-1:0]     i_write_data,
  input                           i_write_enable,
  input      [ADDRESS_WIDTH-1:0]  i_address,
  input      [DATA_WIDTH-1:0]     o_read_data
);

  localparam int DEPTH = 1 << ADDRESS_WIDTH;

  // Lightweight reference model (matches read-before-write and "write => zeroed read" behavior)
  logic [DATA_WIDTH-1:0] ref_mem   [0:DEPTH-1];
  bit                    wrote     [0:DEPTH-1];
  logic                  any_write;
  logic [DATA_WIDTH-1:0] ref_rd_exp;

  // Optional init to zero to mirror DUT param for defined comparisons
  initial begin
    any_write = 1'b0;
    for (int j=0; j<DEPTH; j++) begin
      wrote[j] = 1'b0;
      if (INITIALIZE_TO_ZERO) ref_mem[j] = '0;
    end
  end

  // Model: capture "old mem at addr" for this cycle's read, then perform write
  always_ff @(posedge i_clk) begin
    ref_rd_exp <= ref_mem[i_address];      // Read-before-write value
    if (i_write_enable) begin
      ref_mem[i_address] <= i_write_data;  // Write happens at clock edge
      wrote[i_address]   <= 1'b1;
      any_write          <= 1'b1;
    end
  end

  default clocking cb @(posedge i_clk); endclocking

  // Control signals must be known
  a_ctrl_known: assert property (cb !$isunknown({i_write_enable, i_address})))
    else $error("generic_sram_line_en: X/Z on control");

  // During write, read output must be all zeros (write has priority over read)
  a_write_zero: assert property (cb i_write_enable |-> ##0 (o_read_data == '0))
    else $error("generic_sram_line_en: o_read_data not zero on write");

  // During read (no write), output must equal prior mem content at current address
  a_read_matches: assert property (cb (!i_write_enable && (INITIALIZE_TO_ZERO || wrote[i_address])) |-> ##0 (o_read_data == ref_rd_exp))
    else $error("generic_sram_line_en: read data mismatch");

  // If INIT=0, we don't demand defined data for never-written addresses.
  // If INIT=1 and no writes yet, any read must return zero
  a_init_read_zero: assert property (cb (INITIALIZE_TO_ZERO && !any_write && !i_write_enable) |-> ##0 (o_read_data == '0))
    else $error("generic_sram_line_en: init-to-zero read mismatch");

  // Write data should be known when writing
  a_write_data_known: assert property (cb i_write_enable |-> !$isunknown(i_write_data))
    else $error("generic_sram_line_en: X/Z on write data");

  // Targeted RAW check: write then read same address next cycle returns the written data
  a_raw_next: assert property (cb i_write_enable ##1 (!i_write_enable && (i_address == $past(i_address))) |-> ##0 (o_read_data == $past(i_write_data)))
    else $error("generic_sram_line_en: RAW next-cycle mismatch");

  // Coverage
  c_write_then_read_same: cover property (cb i_write_enable ##1 (!i_write_enable && (i_address == $past(i_address)) ) ##0 (o_read_data == $past(i_write_data)));
  c_back_to_back_writes_same: cover property (cb i_write_enable ##1 (i_write_enable && (i_address == $past(i_address))));
  c_read_only: cover property (cb !i_write_enable);
  c_write_only: cover property (cb i_write_enable);
  c_init_read_zero: cover property (cb (INITIALIZE_TO_ZERO && !any_write && !i_write_enable) ##0 (o_read_data == '0));

endmodule

bind generic_sram_line_en
  generic_sram_line_en_sva #(
    .DATA_WIDTH(DATA_WIDTH),
    .ADDRESS_WIDTH(ADDRESS_WIDTH),
    .INITIALIZE_TO_ZERO(INITIALIZE_TO_ZERO)
  ) u_generic_sram_line_en_sva (
    .i_clk(i_clk),
    .i_write_data(i_write_data),
    .i_write_enable(i_write_enable),
    .i_address(i_address),
    .o_read_data(o_read_data)
  );