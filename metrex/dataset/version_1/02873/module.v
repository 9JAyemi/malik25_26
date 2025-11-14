module top_module(
    input [99:0] a, b, // Input ports for 100-bit binary numbers
    input cin, // Carry-in input for 100-bit binary adder
    input clk, // Clock input for 4-bit binary counter
    input reset, // Synchronous active-high reset input for 4-bit binary counter
    output [99:0] sum // Output port for final 100-bit sum
);

    wire [99:0] adder_out;
    wire [3:0] counter_out;
    wire [99:0] final_sum;

    // Instantiate the 100-bit binary adder
    binary_adder adder_inst(
        .a(a),
        .b(b),
        .cin(cin),
        .sum(adder_out),
        .cout()
    );

    // Instantiate the 4-bit binary counter
    binary_counter counter_inst(
        .clk(clk),
        .reset(reset),
        .out(counter_out)
    );

    // Instantiate the functional module that adds the output of the adder to the counter value
    functional_module func_inst(
        .adder_out(adder_out),
        .counter_out(counter_out),
        .final_sum(final_sum)
    );

    // Assign the final sum to the output port
    assign sum = final_sum;

endmodule

// 100-bit binary adder module
module binary_adder(
    input [99:0] a, b, // Input ports for 100-bit binary numbers
    input cin, // Carry-in input
    output reg [99:0] sum, // Output port for sum
    output reg cout // Output port for carry-out
);

    always @(*) begin
        {cout, sum} = a + b + cin;
    end

endmodule

// 4-bit binary counter module
module binary_counter(
    input clk, // Clock input
    input reset, // Synchronous active-high reset input
    output reg [3:0] out // Output port for counter value
);

    always @(posedge clk) begin
        if (reset) begin
            out <= 4'b0;
        end else begin
            out <= out + 1;
        end
    end

endmodule

// Functional module that adds the output of the adder to the counter value
module functional_module(
    input [99:0] adder_out, // Input port for output of 100-bit binary adder
    input [3:0] counter_out, // Input port for output of 4-bit binary counter
    output reg [99:0] final_sum // Output port for final sum
);

    always @(*) begin
        final_sum = adder_out + {96'b0, counter_out};
    end

endmodule