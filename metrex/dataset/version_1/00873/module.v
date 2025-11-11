module binary_adder (
    input [99:0] a, b,     // Inputs to the binary adder
    input cin,             // Carry-in for the binary adder
    output cout,           // Carry-out from the binary adder
    output [99:0] sum      // Sum output from the binary adder
);

    wire [100:0] adder_out; // Internal wire to hold the adder output

    // Ripple-carry adder architecture
    assign adder_out = {cin, a} + {1'b0, b};
    assign cout = adder_out[100];
    assign sum = adder_out[99:0];

endmodule

module shift_register (
    input clk,             // Clock input for the shift register
    input d,               // Input to the shift register
    output q              // Output from the shift register
);

    reg [2:0] shift_reg;    // Internal register to hold the shift register state

    always @(posedge clk) begin
        shift_reg <= {d, shift_reg[2:1]};
    end

    assign q = shift_reg[0];

endmodule

module functional_module (
    input [99:0] adder_sum, // Input from binary adder
    input shift_q,         // Input from shift register
    output [102:0] out     // Final output
);

    wire [102:0] final_out; // Internal wire to hold the final output

    assign final_out = {adder_sum, shift_q};

    assign out = final_out;

endmodule

module top_module (
    input [99:0] a, b,     // Inputs to the binary adder
    input cin,             // Carry-in for the binary adder
    output cout,           // Carry-out from the binary adder
    output [99:0] sum,     // Sum output from the binary adder
    input clk,             // Clock input for the shift register
    input d,               // Input to the shift register
    output q,              // Output from the shift register
    output [102:0] out     // Final output from the functional module
);

    binary_adder adder_inst (
        .a(a),
        .b(b),
        .cin(cin),
        .cout(cout),
        .sum(sum)
    );

    shift_register shift_reg_inst (
        .clk(clk),
        .d(d),
        .q(q)
    );

    functional_module func_inst (
        .adder_sum(sum),
        .shift_q(q),
        .out(out)
    );

endmodule