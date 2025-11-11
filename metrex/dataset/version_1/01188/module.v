module single_port_ram #(
  parameter addr_width = 8,
  parameter data_width = 8
)(
  input clock,
  input [addr_width-1:0] addr,
  input [data_width-1:0] data,
  input we,
  output reg [data_width-1:0] out
);

  parameter mem_depth = 1024;

  reg [data_width-1:0] Mem [0:mem_depth-1];

  always @(posedge clock) begin
    if (we) begin
      Mem[addr] <= data;
    end
    out <= Mem[addr];
  end

endmodule