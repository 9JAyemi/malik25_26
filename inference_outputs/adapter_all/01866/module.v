module up_counter(clk, rst_n, count);
    input clk, rst_n;
    output reg [15:0] count;
    
    always @(posedge clk)
    begin
        if (rst_n == 1'b0)
            count <= 16'b0000000000000000;
        else
            count <= count + 1'b1;
    end
endmodule
