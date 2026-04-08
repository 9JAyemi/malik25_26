module DemoInterconnect_jtag_axi_0_0_rd_status_flags_as__parameterized0_22 (
  output reg out,
  input [1:0] dest_out_bin_ff_reg,
  input aclk
);

  reg [1:0] dest_out_bin_ff_reg_internal;
  reg ram_empty_fb_i;
  reg ram_empty_i;

  always @(posedge aclk) begin
    ram_empty_fb_i <= dest_out_bin_ff_reg[1];
  end

  always @(posedge aclk) begin
    ram_empty_i <= ram_empty_fb_i;
  end

  always @* begin
    out = ram_empty_fb_i;
  end

endmodule