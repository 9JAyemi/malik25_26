
module dff_module (
    input clk,
    input reset,
    input [7:0] d,
    output reg [7:0] q
);

    always @(posedge clk) begin
        if (reset) begin
            q <= 8'h5A;
        end else begin
            q <= d;
        end
    end

endmodule
module top_module (
    input clk,
    input reset,
    input [7:0] d,
    output [7:0] q
);

    wire [7:0] q_temp;

    dff_module dff0 (.clk(clk), .reset(reset), .d(d), .q(q_temp));

    assign q = q_temp;

endmodule