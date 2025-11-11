module bitwise_op(
    input [99:0] in,
    input op,
    output [99:0] out
);

    assign out = (op == 2'b00) ? (in & in) : 
                 (op == 2'b01) ? (in | in) : 
                 (op == 2'b10) ? (in ^ in) : 
                                 100'b0;

endmodule

module mux_256_to_1(
    input [1023:0] in,
    input [2:0] sel,
    output [3:0] out
);

    wire [7:0] mux_out [0:255];

    genvar i;
    generate
        for (i = 0; i < 256; i = i + 1) begin : mux_block
            assign mux_out[i] = in[(i*4)+:4];
        end
    endgenerate

    assign out = mux_out[sel];

endmodule

module functional_module(
    input [99:0] bitwise_out,
    input [3:0] mux_out,
    output [3:0] out
);

    assign out = bitwise_out ^ mux_out;

endmodule

module top_module( 
    input clk,
    input reset, // Synchronous active-high reset
    input [99:0] in, // Input for the bitwise operation module
    input [1023:0] mux_in, // Input vector for the multiplexer
    input [2:0] sel, // Select input for the multiplexer
    output [3:0] out // Final 4-bit output
);

    wire [99:0] bitwise_out;
    wire [3:0] mux_out;

    bitwise_op bitwise_op_inst (
        .in(in),
        .op(3'b000),
        .out(bitwise_out)
    );

    mux_256_to_1 mux_inst (
        .in(mux_in),
        .sel(sel),
        .out(mux_out)
    );

    functional_module functional_inst (
        .bitwise_out(bitwise_out),
        .mux_out(mux_out),
        .out(out)
    );

endmodule