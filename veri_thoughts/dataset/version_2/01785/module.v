module top_module( 
    input wire [31:0] in,
    output wire [31:0] out_xor,
    output wire [31:0] out_and );

    wire [15:0] lower_half;
    wire [15:0] upper_half;
    wire [15:0] xor_half;
    wire [15:0] and_half;

    // Pipeline stage 1
    pipeline_stage_1 stage_1(
        .in(in),
        .lower_half(lower_half),
        .upper_half(upper_half)
    );

    // Pipeline stage 2
    pipeline_stage_2 stage_2(
        .lower_half(lower_half),
        .upper_half(upper_half),
        .xor_half(xor_half),
        .and_half(and_half)
    );

    // Pipeline stage 3
    pipeline_stage_3 stage_3(
        .xor_half(xor_half),
        .and_half(and_half),
        .out_xor(out_xor),
        .out_and(out_and)
    );

endmodule

// Pipeline stage 1
module pipeline_stage_1(
    input wire [31:0] in,
    output wire [15:0] lower_half,
    output wire [15:0] upper_half
);

    assign lower_half = in[15:0];
    assign upper_half = in[31:16];

endmodule

// Pipeline stage 2
module pipeline_stage_2(
    input wire [15:0] lower_half,
    input wire [15:0] upper_half,
    output wire [15:0] xor_half,
    output wire [15:0] and_half
);

    assign xor_half = lower_half ^ upper_half;
    assign and_half = lower_half & upper_half;

endmodule

// Pipeline stage 3
module pipeline_stage_3(
    input wire [15:0] xor_half,
    input wire [15:0] and_half,
    output wire [31:0] out_xor,
    output wire [31:0] out_and
);

    assign out_xor = {16'b0, xor_half};
    assign out_and = {16'b0, and_half};

endmodule