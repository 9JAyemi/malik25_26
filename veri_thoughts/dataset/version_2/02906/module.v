
module counter_display (
    input clk,
    input reset,               // Synchronous active-high reset
    input direction,           // Input to control the count direction
    output [6:0] seg,          // 7-segment display output
    output reg [3:0] cnt           // 4-bit counter output
);

  // Declare intermediate signals
  wire [7:0] out;
  wire cnt_up, cnt_down;    // Control signals for counter direction

  // Instantiate splitter and XOR modules
  splitter_module splitter(.in({cnt, 4'b0}), .out(out));
  xor_module xor0(.a(cnt[0]), .b(cnt[1]), .out_ff(cnt_up));
  xor_module xor1(.a(cnt[2]), .b(cnt[3]), .out_ff(cnt_down));

  // Assign segment outputs
  assign seg = out;

  // Counter logic
  always @(posedge clk) begin
    if (reset) begin
      cnt <= 4'b0000;
    end else if (direction) begin
      // Count up
      cnt <= cnt + 1'b1;
    end else begin
      // Count down
      cnt <= cnt - 1'b1;
    end
  end

endmodule

module splitter_module (
    input [7:0] in,
    output [7:0] out
);

  assign out = in;

endmodule

module xor_module (
    input a,
    input b,
    output out_ff
);

  assign out_ff = a ^ b; // XOR operation

endmodule
