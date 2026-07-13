
module dff_module (
    input clk,
    input [7:0] d,
    output reg [7:0] q
);

    always @(negedge clk) begin
        q <= d;
    end

endmodule
module top_module (
    input clk,
    input [7:0] d,
    output [7:0] q
);

    dff_module dff0(.clk(clk), .d(d), .q(q));

endmodule