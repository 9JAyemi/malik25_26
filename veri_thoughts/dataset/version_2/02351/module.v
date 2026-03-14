module omsp_sync_cell (

// OUTPUTs
    data_out,                      // Synchronized data output

// INPUTs
    clk,                           // Receiving clock
    data_in,                       // Asynchronous data input
    rst                            // Receiving reset (active high)
);

output              data_out;      // Synchronized data output

input               clk;          // Receiving clock
input               data_in;      // Asynchronous data input
input               rst;          // Receiving reset (active high)



reg  [1:0] data_sync;

always @(posedge clk or posedge rst)
  if (rst) data_sync <=  2'b00;
  else     data_sync <=  {data_sync[0], data_in};

assign     data_out   =   data_sync[1];


endmodule