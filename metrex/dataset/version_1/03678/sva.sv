// SVA for register_file
checker regfile_sva(
  input  logic [1:0]  read_register_port_0,
  input  logic [1:0]  read_register_port_1,
  input  logic [1:0]  write_register,
  input  logic [31:0] write_data,
  input  logic        write_enable,
  input  logic [31:0] read_data_port_0,
  input  logic [31:0] read_data_port_1,
  ref    logic [31:0] registers [0:3]
);

  default clocking cb @(posedge write_enable); endclocking

  // Combinational read correctness (continuous, clockless)
  assert property (read_data_port_0 === registers[read_register_port_0]);
  assert property (read_data_port_1 === registers[read_register_port_1]);
  assert property ((read_register_port_0 == read_register_port_1) |-> (read_data_port_0 === read_data_port_1));

  // Inputs must be known on write edge
  assert property (!$isunknown(write_register) && !$isunknown(write_data) && !($isunknown(write_enable)));

  // Write happens on posedge write_enable; targeted element updates
  assert property (##0 registers[write_register] == write_data);

  // Non-targeted elements do not change on write
  genvar i;
  generate
    for (i = 0; i < 4; i++) begin : g_stable_others
      assert property (##0 ((i != write_register) |-> $stable(registers[i])));
    end
  endgenerate

  // Read-after-write returns new data (same time slot after NBA)
  assert property (##0 ((read_register_port_0 == write_register) |-> (read_data_port_0 === write_data)));
  assert property (##0 ((read_register_port_1 == write_register) |-> (read_data_port_1 === write_data)));

  // Coverage
  cover property (write_register == 2'd0);
  cover property (write_register == 2'd1);
  cover property (write_register == 2'd2);
  cover property (write_register == 2'd3);
  cover property (write_register == $past(write_register)); // back-to-back write to same index
  cover property (##0 (read_register_port_0 == write_register) && (read_data_port_0 === write_data));
  cover property (##0 (read_register_port_1 == write_register) && (read_data_port_1 === write_data));
  cover property (read_register_port_0 == read_register_port_1);
  cover property (read_register_port_0 != read_register_port_1);

endchecker

// Bind into DUT
bind register_file regfile_sva regfile_sva_inst(
  .read_register_port_0(read_register_port_0),
  .read_register_port_1(read_register_port_1),
  .write_register(write_register),
  .write_data(write_data),
  .write_enable(write_enable),
  .read_data_port_0(read_data_port_0),
  .read_data_port_1(read_data_port_1),
  .registers(registers)
);