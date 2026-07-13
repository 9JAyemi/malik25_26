
module not_gate (
    input in,
    output out_not
);
    assign out_not = in ^ 1;
endmodule
module edge_detector (
    input clk,
    input [7:0] in,
    output reg [7:0] out_edge
);
    reg [7:0] prev_in;

    always @(posedge clk) begin
        out_edge <= (in & ~prev_in);
        prev_in <= in;
    end
endmodule
module functional_module (
    input [7:0] in_edge,
    input in_not,
    output [7:0] out_func
);
    assign out_func = in_edge & {8{in_not}};
endmodule
module top_module (
    input clk,
    input [7:0] in,
    output [7:0] out_edge,
    output out_not,
    output [7:0] out_func
);
    wire [7:0] edge_out;
    wire not_out;

    not_gate not_inst (
        .in(in[0]),
        .out_not(not_out)
    );

    edge_detector edge_inst (
        .clk(clk),
        .in(in),
        .out_edge(edge_out)
    );

    functional_module func_inst (
        .in_edge(edge_out),
        .in_not(not_out),
        .out_func(out_func)
    );

    assign out_edge = edge_out;
    assign out_not = not_out;
endmodule