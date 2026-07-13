module top_module (
    input clk,
    input reset,
    input [7:0] in_1,
    input [7:0] in_2,
    input select,
    output [7:0] sum_output,
    output [7:0] or_output
);

    // 2-to-1 MUX
    wire [7:0] selected_input;
    mux_2to1 mux_inst (
        .in_0(in_1),
        .in_1(in_2),
        .select(select),
        .out(selected_input)
    );

    // 8-bit adder
    wire [8:0] sum;
    adder_8bit adder_inst (
        .a(selected_input),
        .b(in_2),
        .sum(sum)
    );

    // Bitwise OR
    assign or_output = selected_input | in_2;

    // Output assignments
    assign sum_output = sum[7:0];

endmodule

// 2-to-1 MUX module
module mux_2to1 (
    input [7:0] in_0,
    input [7:0] in_1,
    input select,
    output reg [7:0] out
);

    always @(*) begin
        if (select == 1'b0) begin
            out = in_0;
        end else begin
            out = in_1;
        end
    end

endmodule

// 8-bit adder module
module adder_8bit (
    input [7:0] a,
    input [7:0] b,
    output reg [8:0] sum
);

    always @(*) begin
        sum = {1'b0, a} + {1'b0, b};
    end

endmodule