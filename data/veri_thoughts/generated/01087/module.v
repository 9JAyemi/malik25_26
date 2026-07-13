module top_module (
    input clk,
    input reset,  // Synchronous active-high reset
    input [7:0] d,  // 8-bit input for the register
    input select,  // Select input to choose between register and counter
    output [7:0] q  // 8-bit output from the addition operation
);

    // Declare internal wires
    wire [7:0] reg_out;
    wire [3:0] counter_out;

    // Instantiate the register module
    reg_module reg_inst (
        .clk(clk),
        .reset(reset),
        .d(d),
        .q(reg_out)
    );

    // Instantiate the counter module
    counter_module counter_inst (
        .clk(clk),
        .reset(reset),
        .q(counter_out)
    );

    // Instantiate the adder module
    adder_module adder_inst (
        .a(select ? reg_out : counter_out),
        .b(select ? counter_out : reg_out),
        .sum(q)
    );

endmodule

// 8-bit register with active high synchronous reset
module reg_module (
    input clk,
    input reset,  // Synchronous active-high reset
    input [7:0] d,  // 8-bit input
    output reg [7:0] q  // 8-bit output
);

    always @(posedge clk) begin
        if (reset) begin
            q <= 8'h34;
        end else begin
            q <= d;
        end
    end

endmodule

// 4-bit binary counter that counts from 0 through 15, with synchronous reset to 0
module counter_module (
    input clk,
    input reset,  // Synchronous active-high reset
    output reg [3:0] q  // 4-bit output
);

    always @(posedge clk) begin
        if (reset) begin
            q <= 4'b0;
        end else begin
            q <= q + 1;
        end
    end

endmodule

// Functional module that adds two 8-bit inputs
module adder_module (
    input [7:0] a,  // 8-bit input a
    input [7:0] b,  // 8-bit input b
    output reg [7:0] sum  // 8-bit output sum
);

    always @(*) begin
        sum = a + b;
    end

endmodule