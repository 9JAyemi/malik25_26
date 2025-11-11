
module binary_counter (
    input clk,
    input reset,   // Synchronous active-high reset
    output [3:1] ena,
    output [15:0] q);
    
    reg [15:0] count;
    
    always @(posedge clk) begin
        if (reset) begin
            count <= 0;
        end else begin
            if (ena[3]) begin
                count <= count + 8'b0001_0000;
            end
            if (ena[2]) begin
                count <= count + 8'b0000_1000;
            end
            if (ena[1]) begin
                count <= count + 8'b0000_0010;
            end
            count <= count + 8'b0000_0001;
        end
    end
    
    assign q = count;
    
    assign ena = {1'b0, 1'b0, 1'b0, 1'b1}; // Enable all bits
    
endmodule