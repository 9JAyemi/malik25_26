
module top_module (
    input clk,
    input reset,  // Synchronous active-high reset
    input [7:0] a,
    input [7:0] b,
    output [11:0] s
);

// Multiplication module
wire [15:0] mult_out;
multiplier multiplier_inst(.a(a), .b(b), .out(mult_out));

// Addition module
wire [7:0] add_out;
adder adder_inst(.a(a), .b(b), .out(add_out));

// Output register
reg [11:0] output_reg;

// Control logic
always @ (posedge clk) begin
    if (reset) begin
        output_reg <= 0;
    end else begin
        output_reg <= {4'b0, mult_out[15:8]};  // Always perform multiplication
    end
end

assign s = output_reg;

endmodule
module multiplier (
    input [7:0] a,
    input [7:0] b,
    output [15:0] out
);

assign out = a * b;  // Perform 8-bit multiplication

endmodule
module adder (
    input [7:0] a,
    input [7:0] b,
    output [7:0] out
);

assign out = a + b;

endmodule