module RetimeWrapper_580(
  input         clock,
  input         reset,
  input  [39:0] io_in,
  output [39:0] io_out
);
  wire [39:0] sr_out;
  wire [39:0] sr_in;
  wire  sr_flow;
  wire  sr_reset;
  wire  sr_clock;
  
  RetimeShiftRegister #(.WIDTH(40), .STAGES(1)) sr (
    .out(sr_out),
    .in(sr_in),
    .flow(sr_flow),
    .reset(sr_reset),
    .clock(sr_clock)
  );

  assign io_out = sr_out;
  assign sr_in = io_in;
  assign sr_flow = 1'b1;
  assign sr_reset = reset;
  assign sr_clock = clock;
endmodule

module RetimeShiftRegister #(
  parameter WIDTH = 8,
  parameter STAGES = 1
)(
  output reg [WIDTH-1:0] out,
  input [WIDTH-1:0] in,
  input flow,
  input reset,
  input clock
);
  
  always @ (posedge clock or posedge reset) begin
    if (reset) begin
      out <= 0;
    end else if (flow) begin
      out <= in;
    end
  end
endmodule