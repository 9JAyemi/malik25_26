// SVA checker for axis_alex
module axis_alex_sva (
  input  logic        aclk,
  input  logic        aresetn,

  input  logic [3:0]  alex_data,
  input  logic        s_axis_tready,
  input  logic [31:0] s_axis_tdata,
  input  logic        s_axis_tvalid,

  input  logic [15:0] int_data_reg,
  input  logic [11:0] int_cntr_reg,
  input  logic [1:0]  int_load_reg,
  input  logic        int_enbl_reg,
  input  logic        int_tready_reg
);

  default clocking cb @(posedge aclk); endclocking
  default disable iff (!aresetn)

  let term      = int_cntr_reg[7] & int_cntr_reg[11];
  let seven_all = &int_cntr_reg[6:0];

  // Reset values
  assert property (!aresetn |-> int_data_reg==16'd0 && int_cntr_reg==12'd0 &&
                              int_load_reg==2'd0 && !int_enbl_reg && !int_tready_reg);

  // Output mappings
  assert property (s_axis_tready == int_tready_reg);
  assert property (alex_data[0] == int_data_reg[15]);
  assert property (alex_data[1] == (int_cntr_reg[6] & ~int_cntr_reg[11]));
  assert property (alex_data[2] == (int_load_reg[0] & int_cntr_reg[6] & int_cntr_reg[11]));
  assert property (alex_data[3] == (int_load_reg[1] & int_cntr_reg[6] & int_cntr_reg[11]));

  // Load/accept behavior
  assert property ((s_axis_tvalid && !int_enbl_reg) |=> (s_axis_tready && int_enbl_reg &&
                    int_data_reg == $past(s_axis_tdata[15:0]) &&
                    int_load_reg == $past(s_axis_tdata[17:16])));
  // No spurious ready while busy request
  assert property ((s_axis_tvalid && int_enbl_reg) |=> !s_axis_tready);

  // Ready is a single-cycle pulse and only caused by a valid when idle
  assert property ($rose(s_axis_tready) |-> $past(s_axis_tvalid && !int_enbl_reg));
  assert property ($rose(s_axis_tready) |=> !s_axis_tready);

  // Enable stays high until termination
  assert property ($rose(int_enbl_reg) |-> int_enbl_reg until_with term);

  // Counter behavior
  assert property ((int_enbl_reg && !term) |=> int_cntr_reg == $past(int_cntr_reg) + 12'd1);
  assert property (!int_enbl_reg |=> int_cntr_reg == $past(int_cntr_reg));
  assert property (term |=> (int_cntr_reg==12'd0 && int_load_reg==2'd0 && !int_enbl_reg));

  // Data shift on 7 LSBs all ones
  assert property (seven_all |=> int_data_reg == {$past(int_data_reg[14:0]),1'b0});

  // Coverage
  cover property (s_axis_tvalid && !int_enbl_reg ##1 s_axis_tready);
  cover property (seven_all);
  cover property (term);
  cover property (alex_data[2]);
  cover property (alex_data[3]);

endmodule

// Bind into DUT (connects to internal regs)
bind axis_alex axis_alex_sva u_axis_alex_sva (
  .aclk(aclk),
  .aresetn(aresetn),
  .alex_data(alex_data),
  .s_axis_tready(s_axis_tready),
  .s_axis_tdata(s_axis_tdata),
  .s_axis_tvalid(s_axis_tvalid),
  .int_data_reg(int_data_reg),
  .int_cntr_reg(int_cntr_reg),
  .int_load_reg(int_load_reg),
  .int_enbl_reg(int_enbl_reg),
  .int_tready_reg(int_tready_reg)
);