
module counter_module (
    input clk,
    input reset, // Synchronous active-high reset
    output [5:0] q, // 6-bit output from the functional module
    output reg [3:0] out1, out2 // Outputs from the two given 4-bit counters
);

reg [3:0] counter1 = 4'b0000; // First 4-bit counter
reg [3:0] counter2 = 4'b0000; // Second 4-bit counter

always @(posedge clk) begin
    if (reset) begin
        counter1 <= 4'b0000;
        counter2 <= 4'b0000;
    end else begin
        counter1 <= counter1 + 1;
        counter2 <= counter2 + 1;
    end
    out1 <= counter1;
    out2 <= counter2;
end

assign q = {counter2, counter1}; // Concatenation of the two counters

endmodule