
module and_gate (
    input wire [7:0] a,
    input wire [7:0] b,
    output wire [7:0] y
);
    assign y = a & b;
endmodule
module not_gate (
    input wire [7:0] a,
    output wire [7:0] y
);
    assign y = ~a;
endmodule
module mux8x1 (
    input wire [7:0] a,
    input wire [7:0] b,
    input wire sel,
    output wire [7:0] y
);
    assign y = (sel) ? b : a;
endmodule
module barrel_shifter (
    input wire [15:0] in,
    output reg [7:0] out1,
    output reg [7:0] out2
);
    always @(*) begin
        out1 = in[15:8];
        out2 = in[7:0];
    end
endmodule
module top_module(
    input wire [7:0] and_input,
    input wire [15:0] shifter_input,
    input wire select,
    output reg [7:0] functional_output
);
    wire [7:0] and_output;
    wire [7:0] shifter_output1;
    wire [7:0] shifter_output2;

    and_gate and_gate_inst (
        .a(and_input),
        .b(and_input),
        .y(and_output)
    );

    barrel_shifter barrel_shifter_inst (
        .in(shifter_input),
        .out1(shifter_output1),
        .out2(shifter_output2)
    );

    always @(*) begin
        if (select) begin
            functional_output = and_output | shifter_output1;
        end else begin
            functional_output = and_output | shifter_output2;
        end
    end
endmodule