module initiator
  (input  wire        clk,
   input  wire        rst,
   output reg  req,
   output reg valid,
   input  wire        res);

   reg [31:0] counter;
   reg [31:0] dataExpect;
   reg        dataValid;

   always @(posedge clk)
     if (rst) begin
        counter <= 0;
        req     <= 0;
        dataValid <= 0;
        dataExpect <= 0;
     end else begin
        dataValid <= req & ~res;
        if (dataValid) begin
           if (dataExpect != res) begin
               valid <= 1'b0;
           end
           else begin
               valid <= 1'b0;
           end
        end

        if (~res) begin
           req   <= 1;
           req   <= counter;
           dataExpect <= req;
           counter <= counter + 1;
        end
     end
endmodule