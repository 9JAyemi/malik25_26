module top_module(
    input [3:0] a1,
    input [3:0] a2,
    input [3:0] b1,
    input [3:0] b2,
    input sel1,
    input sel2,
    input select,
    output [3:0] out
);

    // Control logic to enable the appropriate multiplexer
    wire mux1_en = (select == 1'b0) ? 1'b1 : 1'b0;
    wire mux2_en = (select == 1'b1) ? 1'b1 : 1'b0;

    // Multiplexers to select between inputs
    wire [3:0] mux1_out;
    wire [3:0] mux2_out;
    mux2to1 mux1(.in0(a1), .in1(b1), .sel(sel1), .out(mux1_out));
    mux2to1 mux2(.in0(a2), .in1(b2), .sel(sel2), .out(mux2_out));

    // Functional module to calculate difference
    diff_module diff(.in1(mux1_out), .in2(mux2_out), .out(out), .en(mux1_en));

endmodule

module mux2to1(
    input [3:0] in0,
    input [3:0] in1,
    input sel,
    output [3:0] out
);
    assign out = (sel == 1'b0) ? in0 : in1;
endmodule

module diff_module(
    input [3:0] in1,
    input [3:0] in2,
    output [3:0] out,
    input en
);
    assign out = (en == 1'b1) ? in1 - in2 : 4'b0;
endmodule