module counter_mux_module (
  input clk,
  input reset,
  output reg [1:0] out
);

reg [2:0] count;

always @(posedge clk) begin
  if (reset) begin
    count <= 0;
  end else begin
    if (count == 6) begin
      count <= 0;
    end else begin
      count <= count + 1;
    end
  end
end

always @* begin
  case (count)
    0: out = 2'b00;
    1: out = 2'b01;
    2, 3: out = 2'b10;
    4, 5, 6: out = 2'b11;
  endcase
end

endmodule
module top_module (
  input clk,
  input reset,
  output [7:0] out
);

wire [1:0] out_sub [3:0];

counter_mux_module sub_inst1 (
  .clk(clk),
  .reset(reset),
  .out(out_sub[0])
);

counter_mux_module sub_inst2 (
  .clk(clk),
  .reset(reset),
  .out(out_sub[1])
);

counter_mux_module sub_inst3 (
  .clk(clk),
  .reset(reset),
  .out(out_sub[2])
);

counter_mux_module sub_inst4 (
  .clk(clk),
  .reset(reset),
  .out(out_sub[3])
);

assign out[1:0] = out_sub[0];
assign out[3:2] = out_sub[1];
assign out[5:4] = out_sub[2];
assign out[7:6] = out_sub[3];

endmodule
