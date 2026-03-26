
module top_module (
    input clk,
    input reset,         // Synchronous active-high reset
    input [1:0] counter, // Configurable 3-bit counter
    input a,             // Input for first XOR gate
    input b,             // Input for second XOR gate
    output wire out       // Output from functional module
);

reg [2:0] counter_reg;   // Register to hold current counter value

wire [1:0] counter_ls;   // Least significant bits of counter
wire [1:0] counter_ms;   // Most significant bits of counter

wire xor1_out;           // Output from first XOR gate
wire xor2_out;           // Output from second XOR gate

// Instantiate XOR gates
xor_gate xor1(.a(counter_ls[0]), .b(counter_ls[1]), .out(xor1_out));
xor_gate xor2(.a(counter_ms[0]), .b(counter_ms[1]), .out(xor2_out));

// Instantiate functional module for final XOR operation
xor_gate final_xor(.a(xor1_out), .b(xor2_out), .out(out));

// Counter logic
always @(posedge clk) begin
    if (reset) begin
        counter_reg <= 3'b000;
    end else begin
        counter_reg <= counter_reg + 1;
    end
end

// Assign counter bits to wires
assign counter_ls = counter_reg[1:0];
assign counter_ms = counter_reg[2:1];

endmodule
module xor_gate (
    input a,
    input b,
    output wire out
);

assign out = a ^ b;

endmodule