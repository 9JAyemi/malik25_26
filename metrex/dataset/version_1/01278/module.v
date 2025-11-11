
module top_module (
    input wire [15:0] in,
    input wire [7:0] a,
    input wire [7:0] b,
    output wire [7:0] out
);

    wire [7:0] upper_byte;
    wire [7:0] lower_byte;
    wire [7:0] sum;
    wire overflow;

    byte_splitter bs(
        .in(in),
        .out_hi(upper_byte),
        .out_lo(lower_byte)
    );

    add_overflow_detection aod_upper(
        .a(a),
        .b(upper_byte),
        .s(sum),
        .overflow(overflow)
    );

    add_overflow_detection aod_lower(
        .a(b),
        .b(lower_byte),
        .s(),
        .overflow()
    );

    assign out = sum;

endmodule
module byte_splitter (
    input wire [15:0] in,
    output wire [7:0] out_hi,
    output wire [7:0] out_lo
);
    assign out_hi = in[15:8];
    assign out_lo = in[7:0];
endmodule
module add_overflow_detection (
    input [7:0] a,
    input [7:0] b,
    output [7:0] s,
    output overflow
);
    reg [8:0] temp_sum;
    assign s = temp_sum[7:0];
    assign overflow = (temp_sum[8] == 1);

    always @(*) begin
        temp_sum = a + b;
    end

endmodule