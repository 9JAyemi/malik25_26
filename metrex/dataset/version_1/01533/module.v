module consecutive_ones_counter (
  input clk,
  input reset,
  input [3:0] data,
  output reg [2:0] count
);

reg [2:0] count_reg;
reg [2:0] count_next;

always @(posedge clk) begin
  if (reset) begin
    count_reg <= 3'b000;
  end else begin
    count_reg <= count_next;
  end
end

always @* begin
  count_next = 3'b000;
  if (data[0] == 1) begin
    count_next = 3'b001;
    if (data[1] == 1) begin
      count_next = 3'b010;
      if (data[2] == 1) begin
        count_next = 3'b011;
      end
    end
  end
end

always @* begin
  count = count_reg;
end

endmodule