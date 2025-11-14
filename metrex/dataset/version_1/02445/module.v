
module top_module (
    input clk,
    input reset,
    input [31:0] in,
    output out
);

    // Declare signals
    wire transition_detected;
    wire equal_a_b;

    // Instantiate the transition detector module
    transition_detector td (
        .clk(clk),
        .reset(reset),
        .in(in),
        .transition_detected(transition_detected)
    );

    // Instantiate the 4-bit comparator module
    four_bit_comparator fbc (
        .a(in[31:28]),
        .b(in[27:24]),
        .equal(equal_a_b)
    );

    // Instantiate the functional module
    functional_module fm (
        .clk(clk),
        .reset(reset),
        .in(in),
        .equal(equal_a_b),
        .out(out)
    );

endmodule
module transition_detector (
    input clk,
    input reset,
    input [31:0] in,
    output reg transition_detected
);

    reg [31:0] prev_in;

    always @ (posedge clk) begin
        if (reset) begin
            prev_in <= 0;
            transition_detected <= 0;
        end else begin
            if ((~prev_in[31] && in[31]) || (prev_in[31] && ~in[31])) begin
                transition_detected <= 1;
            end else begin
                transition_detected <= 0;
            end
            prev_in <= in;
        end
    end

endmodule
module four_bit_comparator (
    input [3:0] a,
    input [3:0] b,
    output reg equal
);

    always @ (*) begin
        if (a == b) begin
            equal <= 1;
        end else begin
            equal <= 0;
        end
    end

endmodule
module functional_module (
    input clk,
    input reset,
    input [31:0] in,
    input equal,
    output out
);

    reg [127:0] pattern = 128'h0000FFFF0000FFFF0000FFFF0000FFFF;
    reg [31:0] pattern_index;

    always @ (posedge clk) begin
        if (reset) begin
            pattern_index <= 0;
        end else begin
            if (equal) begin
                pattern_index <= pattern_index + 1;
            end
            if (pattern_index == 31) begin
                pattern_index <= 0;
            end
        end
    end

    assign out = pattern[pattern_index];

endmodule