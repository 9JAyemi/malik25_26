
module binary_counter(input clk, rst, en, output reg [3:0] count);

  reg [3:0] next_count;
  reg carry_out;

  always @(*) begin
    if (rst) begin
      next_count = 4'b0;
    end
    else if (en) begin
      next_count = count + 1'b1;
    end
    else begin
      next_count = count;
    end
  end

  always @(posedge clk) begin
    count <= next_count;
  end

  always @(*)
  if (count == 4'b1111)
      carry_out = 1'b1;
  else
      carry_out = 1'b0;
endmodule