module system_controller(
   clk_sys, reset_sys, locked,
   clk_in, reset_in
   );
   input wire clk_in;
   output wire clk_sys;
   input  wire reset_in;
   output wire reset_sys;   
   output wire locked;
   
    
   `ifdef XILINX
   wire                         xclk_buf;
   IBUFG xclk_ibufg(.I(clk_in), .O(xclk_buf));
   wire                         locked;
`else
   assign locked = 1;
   
`endif
   

   reg [5:0]                    reset_count = 6'h0;
   assign reset_sys = reset_in | ~locked | (|reset_count);   
   
   always @(posedge clk_in)
     if (reset_in | ~locked) begin
        reset_count <= 6'h1;        
     end else begin
        if (reset_count) begin
           reset_count <= reset_count + 1;           
        end
     end
   
   `ifdef XILINX   
   BUFG clk_bug (
                 .O(clk_sys), .I(CLKFBOUT) );

   clk_wiz_0 lab9_clocks
     (
      .clk_in1(xclk_buf),      .clk_out1(CLKFBOUT),     .reset(reset_in), .locked(locked));      `else assign clk_sys = clk_in;   
   
`endif endmodule 