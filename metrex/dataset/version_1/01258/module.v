
module parity_checker (
  input [7:0] in,
  output [8:0] out
);
  assign out[8] = ^in;
  assign out[7:0] = {in[6:4], in[2:0]};
endmodule

module edge_detector (
  input clk,
  input reset,
  input in,
  output rise,
  output down
);
  reg [1:0] dff_out;
  always @(posedge clk, negedge reset) begin
    if (reset == 0) begin
      dff_out <= 2'b0;
    end else begin
      dff_out <= {dff_out[0], in};
    end
  end
  assign rise = (dff_out[0] == 1'b1) && (dff_out[1] == 1'b0);
  assign down = (dff_out[0] == 1'b0) && (dff_out[1] == 1'b1);
endmodule

module active_signal (
  input [8:0] parity_in,
  input rise_in,
  input down_in,
  output active_out
);
  assign active_out = ((parity_in[8] == 1'b0 && rise_in == 1'b1) || (parity_in[8] == 1'b1 && down_in == 1'b1)) ? 1'b1 : 1'b0;
endmodule

module top_module (
  input               clk,
  input               reset,
  input [7:0]         in,
  output [8:0]    parity_out,
  output          rise,
  output          down,
  output          active
);

  parity_checker parity_checker_inst (
    .in(in),
    .out(parity_out)
  );

  edge_detector edge_detector_inst (
    .clk(clk),
    .reset(reset),
    .in(in[0]),
    .rise(rise),
    .down(down)
  );

  active_signal active_signal_inst (
    .parity_in(parity_out),
    .rise_in(rise),
    .down_in(down),
    .active_out(active)
  );

endmodule
