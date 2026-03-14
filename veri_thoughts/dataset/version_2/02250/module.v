module top_module (
    input clk,
    input reset,      // Synchronous active-high reset
    input [7:0] d,    // 8-bit input for the register
    output [3:0] counter_out, // 4-bit output from the counter
    output [7:0] register_out, // 8-bit output from the register
    output [7:0] final_out // Sum of the counter and register outputs
);

    wire [3:0] counter_out_wire;
    wire [7:0] register_out_wire;
    wire [7:0] final_out_wire;

    counter_module counter_inst (
        .clk(clk),
        .reset(reset),
        .q(counter_out_wire)
    );

    register_module register_inst (
        .clk(clk),
        .reset(reset),
        .d(d),
        .q(register_out_wire)
    );

    functional_module functional_inst (
        .counter_in(counter_out_wire),
        .register_in(register_out_wire),
        .final_out(final_out_wire)
    );

    assign counter_out = counter_out_wire;
    assign register_out = register_out_wire;
    assign final_out = final_out_wire;

endmodule

module counter_module (
    input clk,
    input reset,
    output reg [3:0] q // 4-bit output
);

    always @(posedge clk) begin
        if (reset) begin
            q <= 4'b0000;
        end else begin
            q <= q + 1;
        end
    end

endmodule

module register_module (
    input clk,
    input reset,
    input [7:0] d,
    output reg [7:0] q // 8-bit output
);

    always @(posedge clk) begin
        if (reset) begin
            q <= 8'h34;
        end else begin
            q <= d;
        end
    end

endmodule

module functional_module (
    input [3:0] counter_in,
    input [7:0] register_in,
    output reg [7:0] final_out // Sum of the counter and register inputs
);

    always @(*) begin
        final_out = counter_in + register_in;
    end

endmodule