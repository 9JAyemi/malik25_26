
module d_flip_flop (
    input  clk,
    input  d,
    output q
);

    reg  q_reg;
    assign q = q_reg;

    always @(posedge clk) begin
        q_reg <= d;
    end

endmodule

module jk_flip_flop (
    input  clk,
    input  j,
    input  k,
    output q
);

    reg  q_reg;
    assign q = q_reg;

    always @(posedge clk) begin
        if (j && ~k) begin
            q_reg <= 1'b1;
        end else if (~j && k) begin
            q_reg <= 1'b0;
        end else if (j && k) begin
            q_reg <= ~q_reg;
        end
    end

endmodule

module top_module (
    input  clk,
    input  d,
    output q
);

    wire q_wire;

    d_flip_flop d_ff (
        .clk(clk),
        .d(d),
        .q(q_wire)
    );

    assign q = q_wire;

endmodule
