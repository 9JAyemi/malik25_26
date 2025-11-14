
module top_module (
    input clk,
    input reset,      // Synchronous active-high reset
    input select,     // Select input to choose between multiplexers
    input [3:0] a,    // 4-bit input for the first multiplexer
    input [3:0] b,    // 4-bit input for the first multiplexer
    input [3:0] c,    // 4-bit input for the second multiplexer
    input [3:0] d,    // 4-bit input for the second multiplexer
    output reg [3:0] out  // 4-bit output from the functional module
);

// Instantiate the multiplexers
wire [3:0] mux1_out;
mux4 mux1 (
    .a(a),
    .b(b),
    .s(select),
    .y(mux1_out)
);

wire [3:0] mux2_out;
mux4 mux2 (
    .a(c),
    .b(d),
    .s(select),
    .y(mux2_out)
);

// Calculate the difference between the selected inputs
wire [3:0] diff_out;
assign diff_out = (select) ? (d - c) : (c - d);

// Add the outputs of the multiplexers and the difference
always @(*) begin
    if (select)
        out <= mux1_out + diff_out;
    else
        out <= mux2_out + diff_out;
end

endmodule
module mux4 (
    input [3:0] a,
    input [3:0] b,
    input s,
    output [3:0] y
);

assign y = (s) ? b : a;

endmodule