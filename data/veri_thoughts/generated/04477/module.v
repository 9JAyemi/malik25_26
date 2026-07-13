module bit_reversal (
    input [7:0] data_in,
    output [7:0] data_out
);
    assign data_out = {data_in[0], data_in[1], data_in[2], data_in[3], data_in[4], data_in[5], data_in[6], data_in[7]};
endmodule


module mux_256_to_1 (
    input [255:0] data_in,
    input [7:0] sel,
    output reg [7:0] data_out
);
    always @(*) begin
        data_out = data_in[sel*8 +: 8];
    end
endmodule

module binary_adder (
    input [7:0] a,
    input [7:0] b,
    input sel,
    output [7:0] out
);

wire [7:0] b_reversed;
wire [7:0] b_selected;

bit_reversal br (
    .data_in(b),
    .data_out(b_reversed)
);

assign b_selected = sel ? b_reversed : b;

assign out = a + b_selected;

endmodule
