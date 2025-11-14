
module synchronous_block_ram(
   clk,    
   ce, oe, we, 
   addr, di, doq
   );    
   
parameter aw = 9;
parameter dw = 32; // Define the operand width here

input   clk;
input   ce;
input   we;
input   oe;	
input [aw-1:0]  addr;
input [dw-1:0]  di;

output [dw-1:0] doq;

reg [dw-1:0]    mem [(1<<aw)-1:0] ;
reg [aw-1:0]    addr_reg;		


// memory read address register for synchronous access
always @(posedge clk) begin
    if (ce)
        addr_reg <=  addr;
end
        
// Data output 
assign doq = mem[addr_reg];

always @(posedge clk) begin
    if (we && ce)
        mem[addr] <=  di; 
end
   
endmodule