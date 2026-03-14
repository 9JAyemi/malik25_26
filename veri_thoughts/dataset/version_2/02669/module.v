
module top_module(
    input signed [31:0] a,
    input signed [31:0] b,
    output signed [63:0] product
);

    wire signed [15:0] stage1_out;
    wire signed [15:0] stage2_out;
    wire signed [15:0] stage3_out;
    wire signed [15:0] stage4_out;

    // instantiate four 8-bit multiplication modules
    mult8bit mult1(.a(a[7:0]), .b(b[7:0]), .product(stage1_out[15:0]));
    mult8bit mult2(.a(a[15:8]), .b(b[15:8]), .product(stage2_out[15:0]));
    mult8bit mult3(.a(a[23:16]), .b(b[23:16]), .product(stage3_out[15:0]));
    mult8bit mult4(.a(a[31:24]), .b(b[31:24]), .product(stage4_out[15:0]));

    // pipeline structure
    reg signed [15:0] stage1_reg;
    reg signed [15:0] stage2_reg;
    reg signed [15:0] stage3_reg;
    reg signed [15:0] stage4_reg;

    always @(*) begin
        stage1_reg = stage1_out;
    end

    always @(*) begin
        stage2_reg = stage2_out;
    end

    always @(*) begin
        stage3_reg = stage3_out;
    end

    always @(*) begin
        stage4_reg = stage4_out;
    end

    assign product = {stage4_reg, stage3_reg, stage2_reg, stage1_reg};

endmodule
module mult8bit(
    input signed [7:0] a,
    input signed [7:0] b,
    output signed [15:0] product
);

    assign product = a * b;

endmodule