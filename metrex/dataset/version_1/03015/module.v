
module top_module(
  input              clk,
  input              reset,      // Synchronous active-high reset
  input  [7:0]       sel,        // Select input to choose between multiplexer and counter
  input  [1023:0]    in,         // 1024-bit input vector for the multiplexer
  output [3:0]       out,        // 4-bit output of the multiplexer
  output reg [15:0]  Q          // 16-bit output of the Johnson counter
);

  // 256-to-1 multiplexer
  wire [3:0] mux_out;
  assign mux_out = in[sel*4 +: 4];
  assign out = mux_out;

  // 16-bit Johnson counter
  reg [15:0] Q_next;
  always @(posedge clk or posedge reset) begin
    if (reset) begin
      Q_next <= 16'b0000000000000000;
    end else begin
      Q_next <= {Q[14:0], Q[15] ^ Q[14]};
    end
  end
  always @(posedge clk) begin
    Q <= Q_next;
  end

  // Functional module
  reg [3:0] mux_out_delayed; // Changed from wire to reg
  reg [15:0] Q_delayed;
  always @(posedge clk) begin
    mux_out_delayed <= mux_out;
    Q_delayed <= Q;
  end
  reg [19:0] final_output; // Changed from assign 
  always @(*) begin
    final_output = {mux_out_delayed, Q_delayed};
  end // Fixed RTL

endmodule