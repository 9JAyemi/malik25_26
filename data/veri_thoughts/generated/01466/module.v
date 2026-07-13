
module top_module(
    input wire [15:0] in,
    output wire [7:0] out_hi,
    output wire [7:0] out_lo,
    output wire [7:0] out_sum );

    wire [7:0] in_hi = in[15:8];
    wire [7:0] in_lo = in[7:0];

    // Decoder to select which byte to output
    wire [1:0] select;
    wire sel_hi = in_hi[7];
    assign select = {sel_hi, 1'b1};

    // Multiplexer to select which byte to output
    wire [7:0] out_sel;
    assign out_sel = (select == 2'b11) ? in_hi : in_lo;

    // Output ports
    assign out_hi = (sel_hi == 1'b1) ? in_hi : 8'b0;
    assign out_lo = (sel_hi == 1'b0) ? in_lo : 8'b0;

    // Functional module to sum the two bytes
    wire [15:0] in_sum = in_hi + in_lo;
    assign out_sum = in_sum[7:0];

endmodule