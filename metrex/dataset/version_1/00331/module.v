
module memory_interface #(
  parameter AW = 12,
  parameter DW = 32,
  parameter DP = 1024
)(
  input clk,
  input rst_n,
  input icb_cmd_valid,
  output icb_cmd_ready,
  input [AW-1:0] icb_cmd_addr,
  input icb_cmd_read,
  output icb_rsp_valid,
  input icb_rsp_ready,
  output icb_rsp_err,
  output [DW-1:0] icb_rsp_rdata
);

  wire [DW-1:0] mem_dout;
  wire [AW-1:0] mem_addr;
  wire [DW-1:0] mem_din;
  wire mem_we = ~icb_cmd_read;

  assign mem_addr = icb_cmd_addr[AW-1:2];
  assign icb_cmd_ready = 1'b1;

  memory #(
    .AW(AW),
    .DW(DW),
    .DP(DP)
  ) mem (
    .clk(clk),
    .rst_n(rst_n),
    .addr(mem_addr),
    .din(mem_din),
    .dout(mem_dout),
    .we(mem_we)
  );

  assign icb_rsp_rdata = mem_dout;
  assign icb_rsp_valid = (icb_cmd_valid && icb_cmd_ready) ? 1'b1 : 1'b0;
  assign icb_rsp_err = 1'b0;
  assign mem_din = (icb_cmd_read) ? 0 : icb_rsp_rdata;

endmodule
module memory #(
  parameter AW = 12,
  parameter DW = 32,
  parameter DP = 1024
)(
  input clk,
  input rst_n,
  input [AW-1:0] addr,
  input [DW-1:0] din,
  output reg [DW-1:0] dout,
  input we
);

  reg [DW-1:0] mem [DP-1:0];

  always @(posedge clk) begin
    if (!rst_n) begin
      dout <= 0;
    end else begin
      if (we) begin
        mem[addr] <= din;
      end else begin
        dout <= mem[addr];
      end
    end
  end

endmodule