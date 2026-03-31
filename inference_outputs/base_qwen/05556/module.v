module sequence_edge_detection (
    input clk,
    input reset,
    input [3:0] in,
    output reg [3:0] out
);

reg [3:0] prev_in;

always @(posedge clk) begin
    if (reset) begin
        out <= 4'b0;
        prev_in <= 4'b0;
    end else begin
        if (in != prev_in) begin
            out <= in;
            prev_in <= in;
        end
    end
end

endmodule

module change_detection (
    input clk,
    input reset,
    input [31:0] in,
    output reg [31:0] out
);

reg [31:0] prev_in;

always @(posedge clk) begin
    if (reset) begin
        out <= 32'b0;
        prev_in <= 32'b0;
    end else begin
        out <= (prev_in & ~in);
        prev_in <= in;
    end
end

endmodule

module functional_module (
    input [3:0] seq_out,
    input [31:0] change_out,
    output reg [31:0] final_out
);

always @(*) begin
    final_out = (seq_out | change_out);
end

endmodule

module top_module (
    input clk,
    input reset,
    input [35:0] in,
    output [31:0] out
);

wire [3:0] seq_out;
wire [31:0] change_out;
wire [31:0] final_out;

sequence_edge_detection seq_edge_detect (
    .clk(clk),
    .reset(reset),
    .in(in[3:0]),
    .out(seq_out)
);

change_detection change_detect (
    .clk(clk),
    .reset(reset),
    .in(in[35:4]),
    .out(change_out)
);

functional_module func_module (
    .seq_out(seq_out),
    .change_out(change_out),
    .final_out(final_out)
);

assign out = final_out;

endmodule