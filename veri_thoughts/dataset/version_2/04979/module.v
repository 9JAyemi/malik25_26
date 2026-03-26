
module soc_system_jtag_uart_sim_scfifo_w (
  // inputs:
  clk,
  fifo_wdata,
  fifo_wr,

  // outputs:
  fifo_FF,
  r_dat,
  wfifo_empty,
  wfifo_used
);

  output fifo_FF;
  output [7:0] r_dat;
  output wfifo_empty;
  output [5:0] wfifo_used;
  input clk;
  input [7:0] fifo_wdata;
  input fifo_wr;

  wire fifo_FF;
  wire [7:0] r_dat;
  wire wfifo_empty;
  wire [5:0] wfifo_used;

  // Simulation-only contents
  integer write_cnt = 0;
  initial begin
    `ifdef SIM_TIME
      $display("%d: soc_system_jtag_uart_sim_scfifo_w", $time);
    `endif
  end

  always @(posedge clk) begin
    if (fifo_wr) begin
      `ifdef SIM_TIME
        $write("%c", fifo_wdata);
      `endif
      write_cnt = write_cnt + 1;
    end
  end

  assign wfifo_used = write_cnt; // only write, no read, used is the same as write count
  assign r_dat = 8'h00;
  assign fifo_FF = 1'b0;
  assign wfifo_empty = (write_cnt == 0);

endmodule