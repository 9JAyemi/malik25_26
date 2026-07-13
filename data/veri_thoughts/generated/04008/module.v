module binary_logic (
    input [7:0] a,
    input [7:0] b,
    output [7:0] c
);

    assign c = a & b;   // Bit-wise AND operation

endmodule

module binary_storage (
    input clk,
    input reset,            // Synchronous reset
    input [7:0] d,
    output reg [7:0] q
);

    always @(posedge clk) begin
        if (reset) begin
            q <= 8'b0;      // Reset to 0
        end else begin
            q <= d;         // Store input value
        end
    end

endmodule

module top_module (
    input clk,
    input reset,            // Synchronous reset
    input [7:0] d,
    input [7:0] in,
    output [7:0] q
);

    wire [7:0] stored_value;
    binary_storage storage_unit (
        .clk(clk),
        .reset(reset),
        .d(d),
        .q(stored_value)
    );

    binary_logic logic_unit (
        .a(stored_value),
        .b(in),
        .c(q)
    );

endmodule