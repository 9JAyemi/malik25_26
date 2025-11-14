// SVA checker for dual_port_ram
module dual_port_ram_sva #(
  parameter AW = 11,
  parameter DW = 16,
  parameter DEPTH = 1 << AW
)(
  input  logic               clk,
  input  logic [DW-1:0]      data_in,
  input  logic [AW-1:0]      write_addr,
  input  logic               write_en,
  input  logic [AW-1:0]      read_addr,
  input  logic               read_en,
  input  logic [DW-1:0]      data_out
);

  // reference model and init-tracking
  logic                      past_valid;
  logic [DW-1:0]             refmem [0:DEPTH-1];
  bit                        init   [0:DEPTH-1];

  always_ff @(posedge clk) begin
    past_valid <= 1'b1;
    if (write_en) begin
      refmem[write_addr] <= data_in;
      init[write_addr]   <= 1'b1;
    end
  end

  // Inputs known when used
  assert property (@(posedge clk) write_en |-> !$isunknown({write_addr, data_in}));
  assert property (@(posedge clk) read_en  |-> !$isunknown(read_addr));

  // data_out is a hold register: must be stable when no read
  assert property (@(posedge clk) disable iff (!past_valid)
                   !read_en |-> $stable(data_out));

  // Read returns the pre-clock (old) RAM value (read-first semantics)
  assert property (@(posedge clk) disable iff (!past_valid)
                   (read_en && $past(init[read_addr]))
                   |-> data_out == $past(refmem[read_addr]));

  // No X on data_out when reading an initialized location
  assert property (@(posedge clk) disable iff (!past_valid)
                   (read_en && $past(init[read_addr]))
                   |-> !$isunknown(data_out));

  // Read-after-write to same address on the next cycle returns the new data
  assert property (@(posedge clk) disable iff (!past_valid)
                   write_en ##1 (read_en && (read_addr == $past(write_addr)))
                   |-> data_out == $past(data_in));

  // Coverage
  cover property (@(posedge clk) write_en);
  cover property (@(posedge clk) read_en);
  cover property (@(posedge clk) read_en && write_en && (read_addr == write_addr));      // same-addr RW
  cover property (@(posedge clk) read_en && write_en && (read_addr != write_addr));      // diff-addr RW
  cover property (@(posedge clk) write_en ##1 (read_en && (read_addr == $past(write_addr)))); // RAW next
  cover property (@(posedge clk) read_en  && (read_addr  == '0));
  cover property (@(posedge clk) read_en  && (read_addr  == DEPTH-1));
  cover property (@(posedge clk) write_en && (write_addr == '0));
  cover property (@(posedge clk) write_en && (write_addr == DEPTH-1));

endmodule

// Bind example:
// bind dual_port_ram dual_port_ram_sva #(.AW(11), .DW(16)) u_sva (.*);