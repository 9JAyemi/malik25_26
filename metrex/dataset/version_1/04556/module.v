
module dff_chain (
    input clk,
    input reset,
    input [7:0] d,
    output [7:0] q
);

reg [7:0] q_temp;

always @(posedge clk) begin
    if (reset) begin
        q_temp <= 8'h34;
    end else begin
        q_temp <= {q_temp[6:0], d};
    end
end

assign q = q_temp;

endmodule
module top_module (
    input clk,
    input reset,
    input [7:0] d,
    output [7:0] q
);

wire [7:0] dff_output;

dff_chain dff_inst (
    .clk(clk),
    .reset(reset),
    .d(d),
    .q(dff_output)
);

assign q = dff_output;

endmodule