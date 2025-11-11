// SVA for single_port_RAM
// Concise checks for protocol, data integrity (read-first semantics), and coverage.

module single_port_RAM_sva #(
  parameter int data_width = 8,
  parameter int depth      = 256
)(
  input  logic                        clk,
  input  logic                        write_en,
  input  logic                        read_en,
  input  logic [8*depth-1:0]          address,
  input  logic [data_width-1:0]       data_in,
  input  logic [data_width-1:0]       data_out
);

  localparam int ADDR_W = (depth <= 1) ? 1 : $clog2(depth);

  // Init to make $past safe
  bit init;
  always_ff @(posedge clk) init <= 1'b1;

  // Helpers
  wire addr_known = !$isunknown(address);
  wire din_known  = !$isunknown(data_in);
  wire ren_known  = !$isunknown(read_en);
  wire wen_known  = !$isunknown(write_en);

  // Strong range check against the (very wide) address bus
  wire addr_in_range = addr_known && (address < depth);
  wire [ADDR_W-1:0] addr_idx = address[ADDR_W-1:0];

  // Lightweight reference model to check read data
  logic [data_width-1:0] ref_mem [depth-1:0];
  bit                    ref_init[depth-1:0];

  always_ff @(posedge clk) begin
    if (write_en && addr_in_range && din_known) begin
      ref_mem [addr_idx] <= data_in;
      ref_init[addr_idx] <= 1'b1;
    end
  end

  // 1) Control/X checks
  assert_en_known:  assert property (@(posedge clk) ren_known && wen_known)
    else $error("read_en/write_en have X/Z");

  assert_addr_ok_on_access: assert property (@(posedge clk) (write_en || read_en) |-> addr_in_range)
    else $error("Address out of range or X/Z on access");

  assert_din_known_on_write: assert property (@(posedge clk) write_en |-> din_known)
    else $error("data_in has X/Z on write");

  // 2) Output update behavior (registered, only on read)
  assert_dout_changes_only_on_read: assert property (@(posedge clk) $changed(data_out) |-> read_en)
    else $error("data_out changed without read_en");

  assert_hold_when_no_read: assert property (@(posedge clk) !read_en |=> $stable(data_out))
    else $error("data_out not held when read_en=0");

  // 3) Functional correctness: read-first RAM semantics
  // When reading a previously written address, data_out matches the pre-edge contents
  assert_read_matches_model: assert property (@(posedge clk) disable iff (!init)
    (read_en && addr_in_range && ref_init[addr_idx]) |-> (data_out == $past(ref_mem[addr_idx])))
    else $error("Read data mismatch (read-first) vs reference model");

  // When read occurs on initialized location, data_out must be known
  assert_read_not_x_on_init: assert property (@(posedge clk) disable iff (!init)
    (read_en && addr_in_range && ref_init[addr_idx]) |-> !$isunknown(data_out))
    else $error("data_out X/Z on valid read");

  // 4) Simultaneous read/write defined as read-first (old data observed)
  assert_simul_rw_readfirst: assert property (@(posedge clk) disable iff (!init)
    (read_en && write_en && addr_in_range && ref_init[addr_idx]) |-> (data_out == $past(ref_mem[addr_idx])))
    else $error("Simultaneous R/W not read-first");

  // 5) Basic coverage
  cover_write:         cover property (@(posedge clk) write_en && addr_in_range);
  cover_read:          cover property (@(posedge clk) read_en  && addr_in_range);
  cover_simul_rw:      cover property (@(posedge clk) read_en && write_en && addr_in_range);
  cover_min_addr_rd:   cover property (@(posedge clk) read_en  && addr_known && (address == '0));
  cover_max_addr_rd:   cover property (@(posedge clk) read_en  && addr_known && (address == depth-1));
  cover_wr_then_rd:    cover property (@(posedge clk) write_en && addr_in_range ##1 (read_en && (address == $past(address))));

endmodule

// Bind into the DUT
bind single_port_RAM single_port_RAM_sva #(.data_width(data_width), .depth(depth)) u_single_port_RAM_sva (
  .clk      (clk),
  .write_en (write_en),
  .read_en  (read_en),
  .address  (address),
  .data_in  (data_in),
  .data_out (data_out)
);