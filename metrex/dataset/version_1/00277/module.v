
module fifo_async 
   (
   // Outputs
   output full, prog_full, dout, empty, valid,
   // Inputs
   input wr_en, din, rd_en
   );
   
   parameter DW    = 104;        //FIFO width
   parameter DEPTH = 16;          //FIFO depth
   
   reg [DW-1:0] fifo [DEPTH-1:0];
   reg [4:0] wr_ptr;
   reg [4:0] rd_ptr;
   wire [4:0] fifo_count;
   
   assign full = (fifo_count == DEPTH);
   assign prog_full = (fifo_count >= DEPTH-4);
   assign empty = (fifo_count == 0);
   assign valid = (fifo_count > 0);
   assign dout = fifo[rd_ptr];
   
   always @(posedge wr_en) begin
      if(!full) begin
         fifo[wr_ptr] <= din;
         wr_ptr <= wr_ptr + 1;
      end
   end
   
   always @(posedge rd_en) begin
      if(!empty) begin
         rd_ptr <= rd_ptr + 1;
      end
   end
   
   assign fifo_count = wr_ptr - rd_ptr;
   
endmodule