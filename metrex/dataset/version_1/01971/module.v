
module top_module (
    input clk,
    input reset,      // Synchronous active-high reset
    input [3:0] a, b, // Two 4-bit inputs
    input select,     // Select input to choose between adder and subtractor outputs
    output [3:0] out  // 4-bit output from the selected module
);

    // Declare internal wires
    wire [3:0] add_out_int, sub_out_int;

    // Instantiate the adder and subtractor modules
    four_bit_adder adder(.a(a), .b(b), .sum(add_out_int));
    four_bit_subtractor subtractor(.a(a), .b(b), .diff(sub_out_int));

    // Declare a flip-flop for the reset signal
    reg reset_ff;

    // Synchronous active-high reset
    always @(posedge clk) begin
        if (reset) begin
            reset_ff <= 1;
        end else begin
            reset_ff <= 0;
        end
    end

    // Instantiate the select module
    select_module select_inst(.add_out(add_out_int), .sub_out(sub_out_int), .select(select), .out(out));

endmodule

module four_bit_adder (
    input [3:0] a, b, // Two 4-bit inputs
    output [3:0] sum  // 4-bit output from the adder
);

    assign sum = a + b;

endmodule

module four_bit_subtractor (
    input [3:0] a, b, // Two 4-bit inputs
    output [3:0] diff // 4-bit output from the subtractor
);

    assign diff = a - b;

endmodule

module select_module (
    input [3:0] add_out, sub_out, // Outputs from the adder and subtractor modules
    input select,                 // Select input to choose between adder and subtractor outputs
    output [3:0] out              // Final output from the selected module
);

    assign out = select ? add_out : sub_out;

endmodule
