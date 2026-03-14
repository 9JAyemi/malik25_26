module top_module (
    input clk,          // Clock input
    input rst,          // Synchronous active-high reset
    input sel,          // Select input to enable/disable bitwise AND module
    output reg [3:0] q  // 4-bit output from bitwise AND module
);

reg [3:0] counter1;
reg [3:0] counter2;

wire [3:0] and_result;

and_module and_inst (
    .a(counter1),
    .b(counter2),
    .y(and_result)
);

always @(posedge clk) begin
    if (rst) begin
        counter1 <= 4'b0000;
        counter2 <= 4'b0000;
        q <= 4'b0000;
    end else begin
        counter1 <= counter1 + 1;
        counter2 <= counter2 + 1;
        if (sel) begin
            q <= and_result;
        end
    end
end

endmodule

module and_module (
    input [3:0] a,
    input [3:0] b,
    output reg [3:0] y
);

always @(*) begin
    y = a & b;
end

endmodule