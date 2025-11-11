


module Freq_Divider#(
  parameter sys_clk = 50000000,	clk_out = 1				)
  (Clk_in, Clk_out);

  input wire Clk_in;

  output reg Clk_out;
  
parameter max = sys_clk / (2*clk_out); localparam N=log2(max);	reg [N-1:0]counter = 0; always@(posedge Clk_in) begin
    if (counter == max-1)
      begin
        counter <= 0;
        Clk_out <= ~Clk_out;
      end
    else
      begin
        counter <= counter + 1'd1;
      end
  end

  function integer log2(input integer n);
    integer i;
    begin
      log2=1;
      for (i=0; 2**i < n; i=i+1)
        log2=i+1;
    end

  endfunction

endmodule
