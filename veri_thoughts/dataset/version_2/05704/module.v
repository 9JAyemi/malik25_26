
module top_module (
    input clk,
    input reset,
    input [31:0] in,
    input select,
    output q
);

    wire [31:0] out_module1;
    wire q_module2;
    wire [31:0] out_functional;

    module1 module1_inst (
        .clk(clk),
        .reset(reset),
        .in(in),
        .out(out_module1)
    );

    module2 module2_inst (
        .clk(clk),
        .d(out_module1[0]),
        .q(q_module2)
    );

    functional_module functional_module_inst (
        .out_module1(out_module1),
        .q_module2(q_module2),
        .select(select),
        .out(out_functional)
    );

    assign q = out_functional[0];

endmodule
module module1 (
    input clk,
    input reset,
    input [31:0] in,
    output [31:0] out
);

    reg [31:0] out_reg;

    always @(posedge clk) begin
        if (reset) begin
            out_reg <= 0;
        end else begin
            out_reg <= {out_reg[30:0], in[31]};
        end
    end

    assign out = out_reg;

endmodule
module module2 (
    input clk,
    input d,
    output q
);

    reg q_reg;

    always @(posedge clk) begin
        q_reg <= d;
    end

    assign q = q_reg;

endmodule
module functional_module (
    input [31:0] out_module1,
    input q_module2,
    input select,
    output [31:0] out
);

    assign out = select ? out_module1 : {31'b0, q_module2};

endmodule