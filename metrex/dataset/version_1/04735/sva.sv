// SVA checker for single_port_RAM
module single_port_RAM_sva #(parameter int n = 8, parameter int depth = 256) (
  input  logic              clk,
  input  logic              write_en,
  input  logic [n-1:0]      data_in,
  input  logic [8-1:0]      address,
  input  logic [n-1:0]      data_out
);

  // Simple golden model for data checks (only updated on writes)
  logic                     past_valid;
  logic [n-1:0]             model_mem [0:depth-1];
  logic [depth-1:0]         addr_written; // bit set once an address has been written at least once

  initial begin
    past_valid    = 1'b0;
    addr_written  = '0;
  end

  always_ff @(posedge clk) begin
    past_valid <= 1'b1;
    if (write_en) begin
      model_mem[address]  <= data_in;
      addr_written[address] <= 1'b1;
    end
  end

  // Clocking/disables
  default clocking cb @(posedge clk); endclocking
  default disable iff (!past_valid);

  // Helpful locals
  localparam logic [8-1:0] MAX_ADDR = depth-1;
  localparam logic [n-1:0] ALL1     = {n{1'b1}};

  // -----------------------
  // Assertions (quality > quantity)
  // -----------------------

  // Address must always be within depth
  a_addr_in_range: assert property (address < depth);

  // No X/Z on control/address; data_in must be known on write
  a_ctrl_known:         assert property (!$isunknown({write_en, address}));
  a_din_known_on_write: assert property (write_en |-> !$isunknown(data_in));

  // Read returns the last written data for that address (once written at least once)
  a_read_returns_model: assert property (!write_en && addr_written[address] |-> data_out == model_mem[address]);

  // Write, then next-cycle read of same address returns the written data
  a_write_then_read_same_addr: assert property (
    write_en ##1 (!write_en && address == $past(address)) |-> data_out == $past(data_in)
  );

  // During a write cycle, data_out must hold its previous value (no read path active)
  a_data_out_stable_on_write: assert property (write_en |-> $stable(data_out));

  // When reading, data_out should be known once the address has been written at least once
  a_dout_known_on_valid_read: assert property (!write_en && addr_written[address] |-> !$isunknown(data_out));

  // -----------------------
  // Functional coverage
  // -----------------------

  // Exercise writes and reads
  c_write: cover property (write_en);
  c_read:  cover property (!write_en);

  // Toggle write->read and read->write
  c_wr_to_rd: cover property (write_en ##1 !write_en);
  c_rd_to_wr: cover property (!write_en ##1 write_en);

  // Boundary addresses
  c_write_boundaries: cover property (write_en && (address == '0 || address == MAX_ADDR));
  c_read_boundaries:  cover property (!write_en && (address == '0 || address == MAX_ADDR) && addr_written[address]);

  // Write then read same address next cycle
  c_wr_rd_same_next: cover property (write_en ##1 (!write_en && address == $past(address)));

  // Back-to-back writes (same and different addresses)
  c_b2b_wr_same_addr: cover property (write_en ##1 (write_en && address == $past(address)));
  c_b2b_wr_diff_addr: cover property (write_en ##1 (write_en && address != $past(address)));

  // Data patterns
  c_write_all_zeros: cover property (write_en && data_in == '0);
  c_write_all_ones:  cover property (write_en && data_in == ALL1);

endmodule

// Bind into the DUT
bind single_port_RAM single_port_RAM_sva #(.n(n), .depth(depth)) i_single_port_RAM_sva (
  .clk      (clk),
  .write_en (write_en),
  .data_in  (data_in),
  .address  (address),
  .data_out (data_out)
);