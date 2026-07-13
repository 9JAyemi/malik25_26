
module glitch_free_clock_mux #(
  parameter n = 4
) (
  input [n-1:0] clk,
  output reg clk_out
);

reg [n-1:0] sync_clk1; // synchronized input clock signals in clock domain 1
reg [n-1:0] sync_clk2; // synchronized input clock signals in clock domain 2
reg [n-1:0] sync_clk3; // synchronized input clock signals in clock domain 3
reg [n-1:0] sync_clk4; // synchronized input clock signals in clock domain 4
reg [n-1:0] next_sync_clk; // next synchronized input clock signals
reg [n-1:0] select; // clock signal selection

// Synchronize input clock signals in each clock domain
always @(posedge clk[0]) begin
  sync_clk1 <= clk;
end

always @(posedge clk[1]) begin
  sync_clk2 <= clk;
end

always @(posedge clk[2]) begin
  sync_clk3 <= clk;
end

always @(posedge clk[3]) begin
  sync_clk4 <= clk;
end

// Select input clock signal
always @(*) begin
  case ({sync_clk1[n-1], sync_clk1[n-2], sync_clk1[n-3], sync_clk1[n-4]})
    4'b0000: select = sync_clk1;
    4'b0001: select = sync_clk2;
    4'b0010: select = sync_clk3;
    4'b0011: select = sync_clk4;
    default: select = sync_clk1; // Default to clock domain 1
  endcase
end

// Synchronize selected clock signal
always @(posedge select[n-1]) begin
  next_sync_clk <= select;
end

// Generate glitch-free output clock signal
always @(*) begin
  clk_out = next_sync_clk[n-1] & ~sync_clk1[n-1] | ~next_sync_clk[n-1] & sync_clk1[n-1];
end

endmodule