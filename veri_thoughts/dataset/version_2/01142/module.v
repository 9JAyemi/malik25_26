
module register_module (
    input clk,
    input reset,      // Synchronous active-high reset
    input [7:0] d,    // 8-bit input for the register
    output reg [7:0] q // 8-bit output from the register
);

    always @(posedge clk) begin
        if (reset) begin
            q <= 8'h34; // Reset to 0x34
        end else begin
            q <= d;
        end
    end

endmodule

module counter_module (
    input clk,
    input reset,      // Synchronous active-high reset
    output reg [3:0] q // 4-bit output from the counter
);

    always @(posedge clk) begin
        if (reset) begin
            q <= 4'b0; // Reset to 0
        end else begin
            q <= q + 1;
        end
    end

endmodule

module adder_module (
    input [7:0] a,    // 8-bit input for the adder
    input [3:0] b,    // 4-bit input for the adder
    output [7:0] c    // 8-bit output from the adder
);

    assign c = a + b;

endmodule

module control_module (
    input select,     // Select input to choose between register and counter
    input [7:0] reg_output, // Output from the register module
    input [3:0] counter_output, // Output from the counter module
    output [7:0] active_output // Output from the active module
);

    wire [7:0] adder_input;
    wire [3:0] zero = 4'b0;

    adder_module adder_inst (
        .a(reg_output),
        .b(counter_output),
        .c(adder_input)
    );

    assign active_output = select ? adder_input : {zero, reg_output};

endmodule

module top_module (
    input clk,
    input reset,      // Synchronous active-high reset
    input [7:0] d,    // 8-bit input for the register
    input select,     // Select input to choose between register and counter
    output [7:0] q    // 8-bit output from the active module
);

    wire [7:0] reg_output;
    wire [3:0] counter_output;
    wire [7:0] active_output;

    register_module register_inst (
        .clk(clk),
        .reset(reset),
        .d(d),
        .q(reg_output)
    );

    counter_module counter_inst (
        .clk(clk),
        .reset(reset),
        .q(counter_output)
    );

    control_module control_inst (
        .select(select),
        .reg_output(reg_output),
        .counter_output(counter_output),
        .active_output(active_output)
    );

    assign q = active_output;

endmodule
