
module fifo_data_info (
  // inputs:
  address,
  clk,
  in_port,
  reset_n,

  // outputs:
  readdata
);

  output [31:0] readdata;
  input [1:0] address;
  input clk;
  input [13:0] in_port;
  input reset_n;

  reg [13:0] fifo [0:13];
  reg [3:0] write_ptr;
  reg [3:0] read_ptr;
  reg [3:0] count;

  // Write enable signal
  wire we;
  assign we = (count < 14);

  // Read enable signal
  wire re;
  assign re = (count > 0);

  // Write pointer incrementer
  always @(posedge clk)
    if (we && reset_n)
      write_ptr <= write_ptr + 1;

  // Read pointer incrementer
  always @(posedge clk)
    if (re && reset_n)
      read_ptr <= read_ptr + 1;

  // Count incrementer/decrementer
  always @(posedge clk)
    if (we && reset_n)
      count <= count + 1;
    else if (re && reset_n)
      count <= count - 1;

  // Write data to FIFO
  always @(posedge clk)
    if (we && reset_n)
      fifo[write_ptr] <= in_port;

  // Read data from FIFO
  assign readdata = (re && reset_n) ? fifo[read_ptr] : 0;

endmodule
