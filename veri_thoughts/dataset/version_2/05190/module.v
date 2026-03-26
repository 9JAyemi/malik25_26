module top_module (
    input clk,
    input a,
    input b,
    input sel_b1,
    input sel_b2,
    output reg q
);

    wire mux_out;
    mux_2to1 mux_inst (
        .a(a),
        .b(b),
        .sel(sel_b1),
        .out(mux_out)
    );

    d_flip_flop dff_inst (
        .clk(clk),
        .d(mux_out),
        .q(q)
    );

endmodule

module mux_2to1 (
    input a,
    input b,
    input sel,
    output reg out
);

    always @(*) begin
        if (sel == 1'b0) begin
            out = a;
        end else begin
            out = b;
        end
    end

endmodule

module d_flip_flop (
    input clk,
    input d,
    output reg q
);

    always @(posedge clk) begin
        q <= d;
    end

endmodule