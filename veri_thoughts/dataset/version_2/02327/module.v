
module mux_pipeline(
    input [255:0] in,
    input [7:0] sel,
    output reg out,
    input clk
);

reg [7:0] sel_reg;
reg [7:0] sel_next;

reg [255:0] in_reg;
reg [255:0] in_next;

always @(*) begin
    sel_reg = sel;
end

always @(posedge clk) begin
    sel_next <= sel_reg;
    in_next <= in_reg;
end

always @(posedge clk) begin
    out <= in_next[sel_next];
    in_reg <= in_next;
end

endmodule