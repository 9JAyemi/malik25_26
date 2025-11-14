// SVA for MIB. Bind this file; no DUT edits required.

module MIB_sva #(
  parameter int data_width  = 32,
  parameter int memory_size = 1024
)(
  input  logic                   clk,
  input  logic                   reset,
  input  logic                   enable,
  input  logic [31:0]            address,
  input  logic [data_width-1:0]  write_data,
  input  logic [data_width-1:0]  read_data,
  ref    logic [data_width-1:0]  memory [memory_size/4-1:0]
);

  // Parameter sanity
  initial assert (memory_size % 4 == 0)
    else $error("MIB: memory_size must be a multiple of 4");

  // Clocking and reset gating for temporal checks
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset)

  // Index helper (word address)
  function automatic int unsigned idx(input logic [31:0] a);
    return a[31:2];
  endfunction

  // Basic signal integrity
  a_known_ctrl: assert property (@(posedge clk) !$isunknown({reset, enable}));
  a_known_bus_when_en: assert property (enable |-> !$isunknown({address, write_data}));

  // Reset behavior (synchronous)
  a_reset_rd_zero: assert property (@(posedge clk) reset |-> read_data == '0);

  // Address legality on any access
  a_addr_aligned:   assert property (enable |-> address[1:0] == 2'b00);
  a_addr_in_range:  assert property (enable |-> address < memory_size);

  // Read returns pre-state memory word (due to NBA ordering)
  a_read_prev_mem: assert property (enable |=> read_data == $past(memory[idx(address)]));

  // Write updates memory exactly next cycle at addressed word
  a_write_updates: assert property (enable && (write_data != '0)
                                    |=> memory[idx($past(address))] == $past(write_data));

  // No write when write_data == 0
  a_no_write_on_zero: assert property (enable && (write_data == '0)
                                       |=> memory[idx($past(address))] == $past(memory[idx(address)]));

  // When idle, read_data holds its value
  a_hold_when_idle: assert property (!enable |=> $stable(read_data));

  // Back-to-back write then read same address returns written value
  a_wr_then_rd_same: assert property ( enable && (write_data != '0)
                                       ##1 enable && (address == $past(address))
                                       |-> read_data == $past(write_data) );

  // Compact functional coverage
  c_reset_then_access:  cover property (reset ##1 !reset ##1 enable);
  c_read_only:          cover property (enable && (write_data == '0));
  c_write_min_addr:     cover property (enable && (write_data != '0) && (address == 32'h0));
  c_write_max_addr:     cover property (enable && (write_data != '0) && (address == memory_size-4));
  c_b2b_writes_diff:    cover property (enable && (write_data != '0)
                                        ##1 enable && (write_data != '0) && (address != $past(address)));
endmodule

bind MIB MIB_sva #(.data_width(data_width), .memory_size(memory_size))
  MIB_sva_i (.clk(clk),
             .reset(reset),
             .enable(enable),
             .address(address),
             .write_data(write_data),
             .read_data(read_data),
             .memory(memory));