
module top_module (
    input clk,
    input reset,
    input [7:0] d,
    output [7:0] q
);

    // Define internal signals
    wire [3:0] counter_out;
    wire [7:0] q_ff;
    wire select;
    wire [7:0] select_out;

    // Instantiate the binary counter module
    binary_counter counter (
        .clk(clk),
        .reset(reset),
        .count_out(counter_out)
    );

    // Instantiate the flip-flop module
    flip_flop flipflop (
        .clk(clk),
        .d(select_out),
        .q(q_ff)
    );

    // Define the output of the system
    assign q = select ? q_ff : counter_out;

    // Instantiate the multiplexer module
    mux2to1 mux (
        .sel(select),
        .in0({4'b0000, counter_out}),
        .in1(q_ff),
        .out(select_out)
    );

    // Connect the binary counter output to the select input of the multiplexer
    assign select = counter_out[3];

endmodule
module binary_counter (
    input clk,
    input reset,
    output reg [3:0] count_out
);

    always @(posedge clk) begin
        if (reset) begin
            count_out <= 4'b0000;
        end else begin
            count_out <= count_out + 1;
        end
    end

endmodule
module flip_flop (
    input clk,
    input [7:0] d,
    output reg [7:0] q
);

    always @(posedge clk) begin
        q <= d;
    end

endmodule
module mux2to1 (
    input sel,
    input [7:0] in0,
    input [7:0] in1,
    output reg [7:0] out
);

    always @(sel, in0, in1) begin
        if (sel) begin
            out <= in1;
        end else begin
            out <= in0;
        end
    end

endmodule