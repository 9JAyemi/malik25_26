module top_module (
    input wire clk,
    input wire reset,
    input wire [7:0] a, b, c, d,     // Input ports for the minimum circuit
    input wire [7:0] in_hi,          // Input port for the combinational circuit
    input wire [7:0] in_lo,          // Input port for the combinational circuit
    input wire select,               // Select input to choose between the two given modules
    output wire [7:0] min_out,       // Output port from the minimum circuit
    output wire [15:0] comb_out,     // Output port from the combinational circuit
    output wire [15:0] final_out     // Final output from the functional module
);

// Instantiate the minimum circuit module
minimum_circuit min_circuit(
    .a(a),
    .b(b),
    .c(c),
    .d(d),
    .out(min_out)
);

// Instantiate the combinational circuit module
combinational_circuit comb_circuit(
    .in_hi(in_hi),
    .in_lo(in_lo),
    .out(comb_out)
);

// Instantiate the addictive control logic module
additive_control_logic add_control(
    .select(select),
    .min_out(min_out),
    .comb_out(comb_out),
    .final_out(final_out)
);

endmodule

// Define the minimum circuit module
module minimum_circuit (
    input wire [7:0] a,
    input wire [7:0] b,
    input wire [7:0] c,
    input wire [7:0] d,
    output wire [7:0] out
);

// Find the minimum value of the four input values
assign out = (a < b) ? ((a < c) ? ((a < d) ? a : d) : ((c < d) ? c : d)) : ((b < c) ? ((b < d) ? b : d) : ((c < d) ? c : d));

endmodule

// Define the combinational circuit module
module combinational_circuit (
    input wire [7:0] in_hi,
    input wire [7:0] in_lo,
    output wire [15:0] out
);

// Combine the two input bytes into a half-word
assign out = {in_hi, in_lo};

endmodule

// Define the addictive control logic module
module additive_control_logic (
    input wire select,
    input wire [7:0] min_out,
    input wire [15:0] comb_out,
    output wire [15:0] final_out
);

// Choose between the two given modules based on the select input and compute the final output
assign final_out = (select == 1'b0) ? (min_out + comb_out) : (min_out - comb_out);

endmodule