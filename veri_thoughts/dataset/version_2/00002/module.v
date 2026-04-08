module adder (
    input [7:0] a,
    input [7:0] b,
    output [7:0] s
);

    assign s = a + b;

endmodule

module overflow_detection (
    input [7:0] a,
    input [7:0] b,
    input [7:0] s,
    output overflow
);

    assign overflow = ((a[7] == b[7]) && (a[7] != s[7]));

endmodule

module overflow_indicator (
    input overflow,
    output overflow_detected
);

    assign overflow_detected = (overflow) ? 1'b1 : 1'b0;

endmodule

module top_module (
    input clk,
    input reset,
    input [7:0] a,
    input [7:0] b,
    output [7:0] s,
    output overflow,
    output overflow_detected
);

    wire [7:0] adder_output;
    wire overflow_signal;

    adder adder_inst (
        .a(a),
        .b(b),
        .s(adder_output)
    );

    overflow_detection overflow_inst (
        .a(a),
        .b(b),
        .s(adder_output),
        .overflow(overflow_signal)
    );

    overflow_indicator overflow_indicator_inst (
        .overflow(overflow_signal),
        .overflow_detected(overflow_detected)
    );

    assign s = adder_output;
    assign overflow = overflow_signal;

endmodule