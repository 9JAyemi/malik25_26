
module top_module (
    input clk,
    input reset,
    input a,
    input b,
    input sel_b1,
    output q
);

    wire mux_out;
    wire flip_flop_out;
    wire final_out;

    // 2-to-1 mux
    mux_2to1 mux_inst (
        .a(a),
        .b(b),
        .sel(sel_b1),
        .out(mux_out)
    );

    // Positive edge triggered flip-flop
    posedge_edge_ff ff_inst (
        .clk(clk),
        .data(mux_out),
        .out(flip_flop_out)
    );

    // Functional module
    functional_module func_inst (
        .a(mux_out),
        .b(flip_flop_out),
        .out(final_out)
    );

    // Output
    assign q = final_out;

endmodule
module mux_2to1 (
    input a,
    input b,
    input sel,
    output out
);
    assign out = (sel == 1'b0) ? a : b;
endmodule
module posedge_edge_ff (
    input clk,
    input data,
    output out
);
    reg ff;

    always @(posedge clk) begin
        ff <= data;
    end

    assign out = ff;

endmodule
module functional_module (
    input a,
    input b,
    output out
);
    assign out = a + b;
endmodule