// SVA checker for memory_mux. Bind this checker and provide a sampling clock.
module memory_mux_sva (
  input  logic        clk,

  input  logic        select,

  input  logic        enable_0,
  input  logic        command_0,
  input  logic [31:0] address_0,
  input  logic [31:0] write_data_0,
  input  logic [3:0]  write_mask_0,
  input  logic [31:0] read_data_0,
  input  logic        valid_0,

  input  logic        enable_1,
  input  logic        command_1,
  input  logic [31:0] address_1,
  input  logic [31:0] write_data_1,
  input  logic [3:0]  write_mask_1,
  input  logic [31:0] read_data_1,
  input  logic        valid_1,

  input  logic        enable,
  input  logic        command,
  input  logic [31:0] address,
  input  logic [31:0] write_data,
  input  logic [3:0]  write_mask,
  input  logic [31:0] read_data,
  input  logic        valid
);

  default clocking cb @(posedge clk); endclocking

  // Functional muxing with 4-state checking (X/Z propagate correctly)
  assert property (enable     === (select ? enable_1     : enable_0));
  assert property (command    === (select ? command_1    : command_0));
  assert property (address    === (select ? address_1    : address_0));
  assert property (write_data === (select ? write_data_1 : write_data_0));
  assert property (write_mask === (select ? write_mask_1 : write_mask_0));

  // Read data is broadcast to both requesters
  assert property (read_data_0 === read_data);
  assert property (read_data_1 === read_data);

  // Valid is gated only to the selected requester (4-state accurate)
  assert property (valid_1 === (select    ? valid : 1'b0));
  assert property (valid_0 === (!select   ? valid : 1'b0));

  // When select is known, valid outputs are mutually exclusive
  assert property (!$isunknown(select) |-> !(valid_0 && valid_1));

  // Basic functional coverage
  cover property (select == 1'b0);
  cover property (select == 1'b1);
  cover property ($rose(select));
  cover property ($fell(select));
  cover property (valid && !select &&  valid_0 && !valid_1);
  cover property (valid &&  select && !valid_0 &&  valid_1);

endmodule

// Bind example (provide a sampling clock from the environment):
// bind memory_mux memory_mux_sva u_memory_mux_sva ( .clk(tb_clk), .select(select),
//   .enable_0(enable_0), .command_0(command_0), .address_0(address_0), .write_data_0(write_data_0), .write_mask_0(write_mask_0), .read_data_0(read_data_0), .valid_0(valid_0),
//   .enable_1(enable_1), .command_1(command_1), .address_1(address_1), .write_data_1(write_data_1), .write_mask_1(write_mask_1), .read_data_1(read_data_1), .valid_1(valid_1),
//   .enable(enable), .command(command), .address(address), .write_data(write_data), .write_mask(write_mask), .read_data(read_data), .valid(valid) );