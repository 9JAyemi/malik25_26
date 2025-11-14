module soc_system_jtag_uart_sim_scfifo_w (
  // inputs:
  input clk,
  input [7:0] fifo_wdata,
  input fifo_wr,

  // outputs:
  output reg fifo_FF,
  output reg [7:0] r_dat,
  output reg wfifo_empty,
  output reg [5:0] wfifo_used
);

  reg [7:0] fifo [63:0];
  reg [5:0] head;
  reg [5:0] tail;
  reg [6:0] count;
  wire full = (count == 64);
  wire empty = (count == 0);

  always @(posedge clk) begin
    if (fifo_wr && !full) begin
      fifo[head] <= fifo_wdata;
      head <= head + 1;
      count <= count + 1;
    end
    if (!empty) begin
      r_dat <= fifo[tail];
      tail <= tail + 1;
      count <= count - 1;
    end
  end

  always @* begin
    wfifo_used <= count;
    fifo_FF = full;
    wfifo_empty = empty;
  end

endmodule