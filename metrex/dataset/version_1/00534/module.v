
module top_module(
    input clk,
    input async_reset,      // Asynchronous active-high reset
    input [1:0] ena,
    input [99:0] data,
    output [3:0] q,
    output [99:0] q_out);

    // Counter module
    reg [2:0] counter;
    always @(posedge clk or posedge async_reset) begin
        if (async_reset) begin
            counter <= 0;
        end else if (ena[0]) begin
            counter <= counter + 1;
        end
    end
    
    assign q = counter;

    // Functional module
    reg [99:0] sum;
    always @(negedge clk) begin
        if (ena[1]) begin
            sum <= data[49:0] + data[99:50];
        end
    end
    
    assign q_out = sum;

endmodule