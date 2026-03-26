
module Adder_with_reset(
    input [3:0] A,
    input B,
    input RST,
    input clk,  // Added clock input
    output reg [4:0] Q
);

always @(posedge clk) begin
    if (RST) begin
        Q <= 0;
    end else begin
        Q <= A + B;
    end
end

endmodule
