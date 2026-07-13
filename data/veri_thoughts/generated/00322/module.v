module separate_16_to_8(
    input wire [15:0] in,
    output wire [7:0] out_hi,
    output wire [7:0] out_lo
);

    wire [7:0] shifted_in;
    
    assign shifted_in = in >> 8;
    
    assign out_hi = (in[15:8] == 8'b0) ? shifted_in[7:0] : in[15:8];
    assign out_lo = (in[7:0] == 8'b0) ? in[7:0] : shifted_in[7:0];

endmodule

module top_module( 
    input wire [15:0] in,
    output wire [7:0] out_hi,
    output wire [7:0] out_lo
);

    separate_16_to_8 separate(
        .in(in),
        .out_hi(out_hi),
        .out_lo(out_lo)
    );

endmodule