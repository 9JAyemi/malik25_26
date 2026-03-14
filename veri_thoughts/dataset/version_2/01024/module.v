module dff_with_reset_and_or (
    input clk,
    input reset,            // Asynchronous reset
    input [7:0] d,
    output [7:0] q,
    output or_out
);

reg [7:0] q_reg;
reg or_out_reg;

always @(negedge clk or posedge reset) begin
    if (reset) begin
        q_reg <= 8'b0;
        or_out_reg <= 1'b0;
    end else begin
        q_reg <= d;
        or_out_reg <= q_reg[0] | q_reg[1] | q_reg[2] | q_reg[3] | q_reg[4] | q_reg[5] | q_reg[6] | q_reg[7];
    end
end

assign q = q_reg;
assign or_out = or_out_reg;

endmodule

module top_module (
    input clk,
    input reset,            // Asynchronous reset
    input [7:0] d,
    output [7:0] q,
    output or_out
);

dff_with_reset_and_or dff_inst (
    .clk(clk),
    .reset(reset),
    .d(d),
    .q(q),
    .or_out(or_out)
);

endmodule