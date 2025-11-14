module top_module (
    input clk,
    input reset,
    input [3:0] a,
    input [3:0] b,
    input ctrl,
    output [3:0] out_adder,
    output [2:0] out_comparator
);

wire [3:0] adder_output;
wire [2:0] comparator_output;
wire [3:0] mux_output;

// Instantiate adder module
adder adder_inst (
    .a(a),
    .b(b),
    .sum(adder_output)
);

// Instantiate comparator module
comparator comparator_inst (
    .a(a),
    .b(b),
    .result(comparator_output)
);

// Instantiate multiplexer module
mux4to1 mux_inst (
    .select(ctrl),
    .i0(adder_output),
    .i1(comparator_output),
    .o(mux_output)
);

assign out_adder = mux_output[3:0];
assign out_comparator = mux_output[2:0];

endmodule

module adder (
    input [3:0] a,
    input [3:0] b,
    output [3:0] sum
);
    assign sum = a + b;
endmodule

module comparator (
    input [3:0] a,
    input [3:0] b,
    output [2:0] result
);
    assign result = (a > b) ? 3'b100 : (a == b) ? 3'b010 : 3'b001;
endmodule

module mux4to1 (
    input select,
    input [3:0] i0,
    input [2:0] i1,
    output [3:0] o
);
    assign o = select ? {1'b0, i1} : i0;
endmodule