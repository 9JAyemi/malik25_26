
module dff_8 (
    input clk,
    input reset,            // Asynchronous reset
    input [7:0] d,
    output reg [7:0] q
);

always @ (posedge clk or negedge reset) begin
    if (reset == 1'b0) begin
        q <= 8'b0;
    end else begin
        q <= d;
    end
end
endmodule
module top_module (
    input clk,
    input reset,            // Asynchronous reset
    input [7:0] d,
    output [7:0] q
);

dff_8 dff_0 (.clk(clk), .reset(reset), .d(d), .q(q));

endmodule