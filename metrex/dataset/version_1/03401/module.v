module single_port_ram (
  input wire clk,
  input wire en,
  input wire we,
  input wire [10:0] addr,
  input wire [7:0] din,
  output reg [7:0] dout
);

  reg [7:0] ram [0:2047]; // 2^11 bytes

  always @(posedge clk) begin
    if (en) begin
      if (we) begin
        ram[addr] <= din;
      end
      else begin
        dout <= ram[addr];
      end
    end
  end

endmodule