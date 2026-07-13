module top_module (
    input clk,
    input rst,
    input [7:0] d1,
    input [7:0] d2,
    input sel,
    output reg [7:0] q,
    output reg [7:0] sum
);

reg [7:0] d_ff;

// 2-to-1 multiplexer
always @* begin
    d_ff = sel ? d2 : d1;
end

// 8 D flip-flops
always @(posedge clk or posedge rst) begin
    if (rst) begin
        q <= 8'h0;
    end
    else begin
        q <= d_ff;
    end
end

// Additive functional module
always @* begin
    sum <= d1 + d2;
end

endmodule