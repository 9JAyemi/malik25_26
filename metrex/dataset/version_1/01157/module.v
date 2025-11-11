
module oam (
  input [7:0] data_a,
  input [7:0] data_b,
  input [7:0] address_a,
  input [7:0] address_b,
  input clock,
  input wren_a,
  input wren_b,
  output reg [7:0] q_a,
  output reg [7:0] q_b
);

  // Memory for port A
  reg [7:0] memory_a[255:0];

  // Memory for port B
  reg [7:0] memory_b[255:0];

  // Read and write logic for port A
  always @(posedge clock) begin
    if (wren_a)
      memory_a[address_a] <= data_a;
    q_a <= memory_a[address_a];
  end

  // Read and write logic for port B
  always @(posedge clock) begin
    if (wren_b)
      memory_b[address_b] <= data_b;
    q_b <= memory_b[address_b];
  end

endmodule