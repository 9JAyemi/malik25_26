module rotation_module(
  input clk,
  input reset,
  input [3:0] in,
  input load,
  input select,
  input [15:0] data,
  output reg [3:0] out
);

  always @(posedge clk, posedge reset) begin
    if (reset) begin
      out <= 4'b0;
    end
    else if (load) begin
      out <= data[3:0];
    end
    else if (select) begin
      out <= {in[2:0], in[3]};
    end
    else begin
      out <= {in[0], in[3:1]};
    end
  end

endmodule