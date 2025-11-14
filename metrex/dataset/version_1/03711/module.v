module top_module (
  input clk,
  input reset,
  output reg [3:0] binary_number
);

  reg [3:0] binary_num_reg;
  reg [2:0] ones_count_reg;
  
  binary_ones_counter ones_counter(.binary_in(binary_num_reg), .clk(clk), .reset(reset), .ones_count(ones_count_reg));
  
  always @(posedge clk) begin
    binary_num_reg <= binary_num_reg + 1;
  end
  
  always @(posedge clk) begin
    if (ones_count_reg > binary_num_reg) begin
      binary_number <= ones_count_reg;
    end else begin
      binary_number <= binary_num_reg;
    end
  end
  
endmodule

module binary_ones_counter (
  input [3:0] binary_in,
  input clk,
  input reset,
  output reg [2:0] ones_count
);

  always @(posedge clk or posedge reset) begin
    if (reset) begin
      ones_count <= 0;
    end else begin
      case (binary_in)
        4'b0000: ones_count <= 0;
        4'b0001: ones_count <= 1;
        4'b0010: ones_count <= 1;
        4'b0011: ones_count <= 2;
        4'b0100: ones_count <= 1;
        4'b0101: ones_count <= 2;
        4'b0110: ones_count <= 2;
        4'b0111: ones_count <= 3;
        4'b1000: ones_count <= 1;
        4'b1001: ones_count <= 2;
        4'b1010: ones_count <= 2;
        4'b1011: ones_count <= 3;
        4'b1100: ones_count <= 2;
        4'b1101: ones_count <= 3;
        4'b1110: ones_count <= 3;
        4'b1111: ones_count <= 4;
      endcase
    end
  end
  
endmodule