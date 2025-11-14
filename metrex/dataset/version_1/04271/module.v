module top_module (
    input clk,
    input reset, // Synchronous active-high reset
    input [7:0] a, b, // 8-bit inputs for the adder
    input select, // Select input to choose between adder and counter
    output [7:0] q // 8-bit output of the functional module
);

    wire [7:0] adder_out;
    wire [3:0] counter_out;
    wire [7:0] sum;

    adder adder_inst (
        .a(a),
        .b(b),
        .sum(adder_out)
    );

    counter counter_inst (
        .clk(clk),
        .reset(reset),
        .q(counter_out)
    );

    functional functional_inst (
        .adder_out(adder_out),
        .counter_out(counter_out),
        .sum(sum)
    );

    control control_inst (
        .select(select),
        .adder_out(adder_out),
        .counter_out(counter_out),
        .sum(sum),
        .q(q)
    );

endmodule

module adder (
    input [7:0] a,
    input [7:0] b,
    output reg [7:0] sum
);

    always @(*) begin
        sum = a + b;
    end

endmodule

module counter (
    input clk,
    input reset,
    output reg [3:0] q
);

    parameter PERIOD = 16;

    always @(posedge clk) begin
        if (reset) begin
            q <= 0;
        end else if (q == PERIOD - 1) begin
            q <= 0;
        end else begin
            q <= q + 1;
        end
    end

endmodule

module functional (
    input [7:0] adder_out,
    input [3:0] counter_out,
    output reg [7:0] sum
);

    always @(*) begin
        sum = adder_out + (counter_out << 8);
    end

endmodule

module control (
    input select,
    input [7:0] adder_out,
    input [3:0] counter_out,
    input [7:0] sum,
    output reg [7:0] q
);

    always @(*) begin
        if (select) begin
            q = sum + (counter_out << 8);
        end else begin
            q = sum + adder_out;
        end
    end

endmodule