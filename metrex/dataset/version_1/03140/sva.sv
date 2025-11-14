// SVA for mem_interface
module mem_interface_sva #(
  parameter data_width = 32,
  parameter addr_width = 16
)(
  input  logic                   clk,
  input  logic                   rst,
  input  logic                   en,
  input  logic [addr_width-1:0]  addr,
  input  logic                   wr_en,
  input  logic [data_width-1:0]  data_in,
  input  logic [data_width-1:0]  data_out,

  // internal DUT signals
  input  logic [data_width-1:0]  mem_data,
  input  logic [addr_width-1:0]  mem_addr,
  input  logic                   mem_wr_en,
  input  logic                   mem_rd_en
);

  default clocking cb @(posedge clk); endclocking

  // Reset effects (synchronous)
  assert property (rst |=> (mem_wr_en==0 && mem_rd_en==0 && mem_addr=='0 && mem_data=='0));

  // Output mirrors internal
  assert property (data_out == mem_data);

  // Mutual exclusion of RD/WR
  assert property (disable iff (rst) !(mem_wr_en && mem_rd_en));

  // Enable gating: internal enables only come from enabled cycle
  assert property (disable iff (rst) (mem_wr_en || mem_rd_en) |-> $past(en));

  // Address capture when enabled
  assert property (disable iff (rst) en |=> (mem_addr == $past(addr)));

  // Write behavior
  assert property (disable iff (rst) (en && wr_en)
                   |=> (mem_wr_en && !mem_rd_en && (mem_data == $past(data_in))));

  // Read behavior
  assert property (disable iff (rst) (en && !wr_en)
                   |=> (mem_rd_en && !mem_wr_en && (mem_data == '0)));

  // Idle behavior
  assert property (disable iff (rst) !en
                   |=> (!mem_wr_en && !mem_rd_en && (mem_data == '0) && $stable(mem_addr)));

  // No X/Z on key signals after reset released
  assert property (disable iff (rst) !$isunknown({mem_wr_en,mem_rd_en,mem_addr,mem_data,data_out}));

  // Functional coverage
  cover property (rst ##1 !rst);                               // reset release
  cover property (disable iff (rst) en && wr_en);              // a write cycle
  cover property (disable iff (rst) en && !wr_en);             // a read cycle
  cover property (disable iff (rst) !en);                      // an idle cycle
  cover property (disable iff (rst) (en && wr_en) ##1 (en && !wr_en)); // write->read
  cover property (disable iff (rst) (en && !wr_en) ##1 (en && wr_en)); // read->write
  cover property (disable iff (rst) (en && wr_en)[*2]);        // back-to-back writes
  cover property (disable iff (rst) (en && !wr_en)[*2]);       // back-to-back reads
  cover property (disable iff (rst) en ##1 (mem_addr != $past(mem_addr))); // addr change

endmodule

// Bind into all mem_interface instances
bind mem_interface mem_interface_sva #(.data_width(data_width), .addr_width(addr_width)) mem_interface_sva_i (.*);