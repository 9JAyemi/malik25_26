
module clk_generator(
    input clk,
    input en,
    input rst,
    input [31:0] limit,
    input [31:0] count,
    output reg clk_0,
    output reg done
);

    reg [31:0] ndCount;
    reg [31:0] initCount;
    
    initial begin
        clk_0 <= 1'b0;
        ndCount <= 32'h00000000;
        initCount <= count;
    end
    
    always @(posedge clk or negedge rst) begin 
        if(~rst) begin
            clk_0 <= 1'b0;
            ndCount <= 32'h00000000;
            done <= 1'b0;
        end
        else if(en) begin 
            if(ndCount < limit) begin
                ndCount <= ndCount + 1;
                clk_0 <= (ndCount == limit) ? ~clk_0 : clk_0;
                done <= (ndCount == limit) ? 1'b1 : 1'b0;
            end
            else begin
                ndCount <= initCount;
                clk_0 <= 1'b0;
                done <= 1'b1;
            end
        end
        else begin
            ndCount <= initCount;
            clk_0 <= 1'b0;
            done <= 1'b0;
        end
    end

endmodule