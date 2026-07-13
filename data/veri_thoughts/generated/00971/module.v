module add_three_module (
    input [3:0] A, // 4-bit input
    output [3:0] B // 4-bit output
);

    assign B = A + 3; // Add 3 to the input

endmodule

module counter_4bit (
    input clk, // Clock input
    input reset, // Asynchronous reset input
    input enable, // Enable input
    output reg [3:0] count // 4-bit output
);

    always @(posedge clk or negedge reset) begin
        if (reset == 0) begin
            count <= 0; // Reset the counter to 0
        end else if (enable == 1) begin
            count <= count + 1; // Increment the counter
        end
    end

endmodule

module functional_module (
    input [3:0] add_output, // 4-bit output from the add_three_module
    input [3:0] counter_output, // 4-bit output from the counter_4bit module
    output [3:0] final_output // 4-bit final output
);

    assign final_output = add_output + counter_output; // Add the outputs of both modules

endmodule

module top_module (
    input clk, // Clock input
    input reset, // Asynchronous reset input
    input enable, // Enable input
    input [3:0] A, // 4-bit input for the add_three_module
    output [3:0] final_output // 4-bit final output from the functional module
);

    wire [3:0] add_output; // Output from the add_three_module
    wire [3:0] counter_output; // Output from the counter_4bit module

    add_three_module add_inst (
        .A(A),
        .B(add_output)
    );

    counter_4bit counter_inst (
        .clk(clk),
        .reset(reset),
        .enable(enable),
        .count(counter_output)
    );

    functional_module func_inst (
        .add_output(add_output),
        .counter_output(counter_output),
        .final_output(final_output)
    );

endmodule