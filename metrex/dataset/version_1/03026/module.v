
module fifo (
       input  [7:0] io_dataIn,
       output [7:0] io_dataOut,
       input   io_read,
       input   io_write,
       output  io_full,
       output  io_empty,
       input   clk,
       input   reset
     );
     
     localparam DEPTH = 32;
     
     reg [7:0] mem [0:DEPTH-1];
     reg [4:0] head, tail;
     reg [4:0] next_head, next_tail;
     reg full, empty;
     
     assign io_full = full;
     assign io_empty = empty;
     
     always @(posedge clk) begin
         if (reset) begin
             tail <= 0;
             head <= 0;
             empty <= 1;
             full <= 0;
         end else begin
             if (io_write & ~full) begin
                 mem[head] <= io_dataIn;
                 head <= next_head;
             end 
             if (io_read & ~empty) begin
                 tail <= next_tail;
             end
             
             if (next_head == next_tail) begin  
                 full <= io_write;
                 empty <= io_write ? 0 : empty;
             end else begin
                 full <= 0;
                 empty <= (head == tail) ? io_write : empty;
             end
             
             next_head <= head + io_write;
             next_tail <= tail + io_read;
         end
     end
     
     assign io_dataOut = empty ? 0 : mem[tail];
     
 endmodule