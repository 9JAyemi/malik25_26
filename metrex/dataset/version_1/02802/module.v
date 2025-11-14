
module add_sub_edge (
    input clk,
    input [31:0] a,
    input [31:0] b,
    input sub,
    input [7:0] in,
    output [31:0] sum,
    output [7:0] anyedge_result
);

    // Adder-Subtractor Module
    wire [31:0] adder_out;
    wire [31:0] inverted_b = sub ? ~b + 1 : b;
    carry_lookahead_adder adder_inst (
        .a(a),
        .b(inverted_b),
        .cin(sub),
        .sum(adder_out)
    );

    // Edge Detection Module
    reg [7:0] prev_in;
    always @(posedge clk) begin
        prev_in <= in;
    end
    wire [7:0] anyedge_out = (in ^ prev_in);

    // Output Mux
    assign sum = adder_out;
    assign anyedge_result = anyedge_out ? adder_out[7:0] : 8'b0;

endmodule
module carry_lookahead_adder (
    input [31:0] a,
    input [31:0] b,
    input cin,
    output [31:0] sum
);

    wire [31:0] p = a + b;
    wire [31:0] g = a & b;
    wire [31:0] c = {cin, g[30:0]} + {g[31], p[30:0]};
    assign sum = {c[30], p[29:0]};

endmodule