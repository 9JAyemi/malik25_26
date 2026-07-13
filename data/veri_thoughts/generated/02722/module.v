module register_bank (
  input clk,
  input [31:0] data_in,
  input write_en,
  input [4:0] read_address_1,
  input [4:0] read_address_2,
  output reg [31:0] read_data_1,
  output reg [31:0] read_data_2
);

  wire [31:0] ram_data;
  reg [31:0] ram_q_1;
  reg [31:0] ram_q_2;
  assign ram_data = data_in;

  always @(posedge clk) begin
    read_data_1 <= ram_q_1;
    read_data_2 <= ram_q_2;
  end

  always @(posedge clk) begin
    if (write_en) begin
      ram_q_1 <= ram_data;
      ram_q_2 <= ram_data;
    end
  end

endmodule