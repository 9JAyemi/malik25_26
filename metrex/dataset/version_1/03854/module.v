module counter (
  input clk,
  input rst,
  input load,
  input [7:0] data_in,
  output reg [7:0] count,
  output reg max_count
);

  always @(posedge clk or posedge rst)
  begin
    if (rst) begin
      count <= 8'h00;
      max_count <= 1'b0;
    end
    else if (load) begin
      count <= data_in;
      max_count <= 1'b0;
    end
    else begin
      count <= count + 1;
      if (count == 8'hFF) begin
        max_count <= 1'b1;
        count <= 8'h00;
      end
      else begin
        max_count <= 1'b0;
      end
    end
  end

endmodule