
module memory(clk, cen, we, addr, write_data, read_data,
             ram_clk, ram_we_b, ram_address, ram_data, ram_cen_b);

   input clk;            // system clock
   input cen;            // clock enable for gating ZBT cycles
   input we;             // write enable (active HIGH)
   input [18:0] addr;    // memory address
   input [35:0] write_data;   // data to write
   output [35:0] read_data;   // data read from memory
   output ram_clk;       // physical line to ram clock
   output ram_we_b;      // physical line to ram we_b
   output [18:0] ram_address; // physical line to ram address
   output [35:0] ram_data; // physical line to ram data
   output ram_cen_b;     // physical line to ram clock enable

   reg [35:0] ram_data;

   assign ram_cen_b = ~cen;
   assign ram_clk = 1'b0;
   assign ram_we_b = ~we;
   assign ram_address = addr;
   assign read_data = ram_data;

   always @(posedge clk) begin
     if (cen == 1'b1) begin
       if (we == 1'b1) begin
         ram_data <= write_data;
       end
     end
   end

endmodule