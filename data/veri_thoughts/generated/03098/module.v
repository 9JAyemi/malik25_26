module GreaterThan(
    input clk,              // Clock input
    input reset,            // Synchronous reset
    input [7:0] A,          // 8-bit input A
    input [7:0] B,          // 8-bit input B
    output reg result       // Output result, reg type because it's driven by always block
);

// Sequential logic to compare A and B on clock edges, reset on reset signal
always @(posedge clk) begin
    if (reset) begin
        // Reset state, result can be set to 0 or any default value
        result <= 1'b0;
    end else begin
        // Compare A and B and update result accordingly
        result <= (A > B) ? 1'b1 : 1'b0;
    end
end

endmodule
