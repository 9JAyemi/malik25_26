module dffc_64 ( clk, reset, d, q );
    input clk;
    input reset;
    input [63:0] d;
    output reg [63:0] q;
    
    always @(posedge clk) begin
        if (reset) begin
            q <= 64'b0;
        end else begin
            q <= d;
        end
    end
endmodule