
module mux_with_or(
    input [1:0] sel,   // Select inputs
    input [3:0] data,  // Data inputs
    output w,          // Output 1
    output x,          // Output 2
    output y,          // Output 3
    output z           // Output 4
);

    wire [1:0] mux_sel;     // Select inputs for the 2:1 multiplexer
    wire [1:0] mux_data;    // Data inputs for the 2:1 multiplexer
    wire mux_out;           // Output of the 2:1 multiplexer
    wire or_out;            // Output of the OR gate

    // Connect the select inputs to the corresponding inputs of the 2:1 multiplexer
    assign mux_sel = sel;

    // Connect the data inputs to the corresponding inputs of the 2:1 multiplexer
    assign mux_data[0] = data[0];
    assign mux_data[1] = data[1];

    // Implement the 2:1 multiplexer
    assign mux_out = (mux_sel == 2'b00) ? mux_data[0] :
                     (mux_sel == 2'b01) ? mux_data[1] :
                                         mux_data[0]; // Fix: mux_sel should be constant

    // Implement the OR gate
    or_module or_gate(
        .a(mux_out),
        .b(data[3]),
        .c(or_out)
    );

    // Output the results based on the select inputs
    assign w = (sel == 2'b00) ? or_out : mux_data[0];
    assign x = (sel == 2'b01) ? or_out : mux_data[1];
    assign y = (sel == 2'b10) ? or_out : mux_data[1]; // Fix: Multiplexer output should be used
    assign z = (sel == 2'b11) ? or_out : mux_data[0]; // Fix: Multiplexer output should be used

endmodule
module or_module(
    input a,           // Input 1
    input b,           // Input 2
    output c           // Output
);

    assign c = a | b;   // Implement the OR operation

endmodule