
module tracking_camera_system_jtag_uart_0_sim_scfifo_r (
  // inputs:
  input clk,
  input fifo_rd,
  input rst_n,

  // outputs:
  output fifo_EF,
  output [7:0] fifo_rdata,
  output rfifo_full,
  output [5:0] rfifo_used,
  output [6:0] rfifo_entries
);
  reg [31:0] bytes_left;
  reg fifo_rd_d;

  // Generate rfifo_entries for simulation
  assign rfifo_entries = bytes_left[5:0];  // Fix the width

  // Decrement bytes_left on read
  always @(posedge clk) begin
    if (fifo_rd_d) begin
      bytes_left <= bytes_left - 1;
    end
  end

  // Set fifo_rd_d on reset
  always @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
      fifo_rd_d <= 0;
    end else begin
      fifo_rd_d <= fifo_rd;
    end
  end

  // Set fifo_EF and rfifo_full
  assign fifo_EF = (bytes_left == 0);
  assign rfifo_full = (bytes_left > 64);

  // Set fifo_rdata
  assign fifo_rdata = 8'b0;  // Initialize to 0 for now

  // Set rfifo_used
  assign rfifo_used = 64 - rfifo_entries;

endmodule