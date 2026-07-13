module multiplexer_module(
    input [3:0] in0, // 4-bit input 0
    input [3:0] in1, // 4-bit input 1
    input [3:0] in2, // 4-bit input 2
    input [3:0] in3, // 4-bit input 3
    input [1:0] sel, // Selection input for the multiplexer module
    output reg [3:0] out // 4-bit output from the multiplexer module
);

always @(*) begin
    case(sel)
        2'b00: out = in0;
        2'b01: out = in1;
        2'b10: out = in2;
        2'b11: out = in3;
    endcase
end

endmodule

module functional_module(
    input [3:0] in_mux, // Output from the multiplexer module
    input [3:0] in_rev, // Reversed byte ordering of the input
    output reg [3:0] out // Maximum value between the two inputs
);

always @(*) begin
    if(in_mux > in_rev) begin
        out = in_mux;
    end else begin
        out = in_rev;
    end
end

endmodule

module top_module( 
    input [3:0] in0, // 4-bit input 0
    input [3:0] in1, // 4-bit input 1
    input [3:0] in2, // 4-bit input 2
    input [3:0] in3, // 4-bit input 3
    input [1:0] sel, // Selection input for the multiplexer module
    output [3:0] out // 4-bit output from the functional module
);

wire [3:0] mux_out;
wire [3:0] rev_in;

multiplexer_module mux(
    .in0(in0),
    .in1(in1),
    .in2(in2),
    .in3(in3),
    .sel(sel),
    .out(mux_out)
);

assign rev_in = {in3, in2, in1, in0};

functional_module func(
    .in_mux(mux_out),
    .in_rev(rev_in),
    .out(out)
);

endmodule