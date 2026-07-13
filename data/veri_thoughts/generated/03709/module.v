
module pipelined_module (
    input wire [2:0] in_vec,
    output wire [2:0] out_vec,
    output wire o2,
    output wire o1,
    output wire o0,
    input wire clk
);

    wire [2:0] reg1_out;
    wire [2:0] reg2_out;

    reg [2:0] in_reg;
    reg [2:0] reg1_reg;
    reg [2:0] reg2_reg;

    assign out_vec = reg2_out;
    assign o2 = reg2_out[2];
    assign o1 = reg2_out[1];
    assign o0 = reg2_out[0];

    always @ (posedge clk) begin
        in_reg <= in_vec;
        reg1_reg <= in_reg;
        reg2_reg <= reg1_out;
    end

    pipeline_stage1 stage1 (
        .in_vec(in_reg),
        .out_vec(reg1_out),
        .clk(clk)
    );

    pipeline_stage2 stage2 (
        .in_vec(reg1_reg),
        .out_vec(reg2_out),
        .clk(clk)
    );

endmodule
module pipeline_stage1 (
    input wire [2:0] in_vec,
    output wire [2:0] out_vec,
    input wire clk
);

    reg [2:0] reg_out;

    always @ (posedge clk) begin
        reg_out <= in_vec;
    end

    assign out_vec = reg_out;

endmodule
module pipeline_stage2 (
    input wire [2:0] in_vec,
    output wire [2:0] out_vec,
    input wire clk
);

    reg [2:0] reg_out;

    always @ (posedge clk) begin
        reg_out <= in_vec;
    end

    assign out_vec = reg_out;

endmodule