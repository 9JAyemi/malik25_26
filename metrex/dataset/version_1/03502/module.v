
module axi_timer #(
  parameter WIDTH = 8,
  parameter MAX_VALUE = 256
)(
  input clk,
  input rst,
  input load,
  input [WIDTH-1:0] value,
  input enable,
  output reg timer_expired,
  output wire [WIDTH-1:0] current_value
);

  reg [WIDTH-1:0] count;
  always @(posedge clk) begin
    if (rst) begin
      count <= 0;
      timer_expired <= 0;
    end else if (load) begin
      count <= value;
    end else if (enable) begin
      if (count == 0) begin
        timer_expired <= 1;
        count <= MAX_VALUE;
      end else begin
        count <= count - 1;
        timer_expired <= 0;
      end
    end
  end

  assign current_value = count;

endmodule