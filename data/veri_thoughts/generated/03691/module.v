module dff_chain (
    input clk,
    input reset,            // Asynchronous reset
    input [7:0] d,
    output reg [7:0] q
);

reg [7:0] q1, q2, q3;

always @(posedge clk or negedge reset) begin
    if (reset == 0) begin
        q1 <= 1'b0;
        q2 <= 1'b0;
        q3 <= 1'b0;
        q <= 1'b0;
    end else begin
        q1 <= d;
        q2 <= q1;
        q3 <= q2;
        q <= q3;
    end
end

endmodule

module top_module (
    input clk,
    input reset,            // Asynchronous reset
    input [7:0] d,
    output [7:0] q
);

dff_chain dff_inst (
    .clk(clk),
    .reset(reset),
    .d(d),
    .q(q)
);

endmodule