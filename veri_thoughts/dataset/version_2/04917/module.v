module register_with_reset (
    input clk,
    input reset,        // Synchronous active-high reset
    input [7:0] d,      // 8-bit input
    output reg [7:0] q  // 8-bit output
);

    always @(posedge clk) begin
        if (reset) begin
            q <= 8'b0;
        end else begin
            q <= d;
        end
    end

endmodule

module binary_counter_with_reset (
    input clk,
    input reset,           // Synchronous active-high reset
    output reg [3:0] q     // 4-bit output
);

    always @(posedge clk) begin
        if (reset) begin
            q <= 4'b0;
        end else begin
            q <= q + 1;
        end
    end

endmodule

module functional_module (
    input [7:0] a,    // 8-bit input a
    input [3:0] b,    // 4-bit input b
    output reg [7:0] q // 8-bit output
);

    always @(*) begin
        q = a + {4'b0, b};
    end

endmodule

module multiplexer (
    input [7:0] a,    // 8-bit input a
    input [3:0] b,    // 4-bit input b
    input select,     // Select input to choose between a and b
    output reg [7:0] q // 8-bit output
);

    always @(*) begin
        if (select) begin
            q = {4'b0, b};
        end else begin
            q = a;
        end
    end

endmodule

module top_module (
    input clk,
    input reset,        // Synchronous active-high reset
    input [7:0] d,      // 8-bit input for the register
    input select,       // Select input to choose between register and counter
    output [7:0] q      // 8-bit output from the functional module
);

    wire [7:0] register_output;
    wire [3:0] counter_output;
    wire [7:0] functional_output;

    register_with_reset register_inst (
        .clk(clk),
        .reset(reset),
        .d(d),
        .q(register_output)
    );

    binary_counter_with_reset counter_inst (
        .clk(clk),
        .reset(reset),
        .q(counter_output)
    );

    multiplexer mux_inst (
        .a(register_output),
        .b(counter_output),
        .select(select),
        .q(functional_output)
    );

    functional_module functional_inst (
        .a(functional_output),
        .b(counter_output),
        .q(q)
    );

endmodule