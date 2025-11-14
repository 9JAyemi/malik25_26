
module top_module (
    input [7:0] A,
    input [7:0] B,
    input enable,
    output EQ,
    output GT,
    output OR
);

    wire [7:0] mux_output;
    wire EQ_int;
    wire GT_int;

    // 2-to-1 Multiplexer module
    mux_2to1 mux_inst (
        .in0(A),
        .in1(B),
        .sel(enable),
        .out(mux_output)
    );

    // 8-bit Comparator module
    comp_8bit comp_inst (
        .A(mux_output),
        .B(B),
        .EQ(EQ_int),
        .GT(GT_int)
    );

    // OR gate
    assign OR = EQ_int | GT_int;

    assign EQ = EQ_int;
    assign GT = GT_int;

endmodule

module mux_2to1 (
    input [7:0] in0,
    input [7:0] in1,
    input sel,
    output reg [7:0] out
);

    always @(*) begin
        if(sel == 0)
            out = in0;
        else
            out = in1;
    end
endmodule

module comp_8bit (
    input [7:0] A,
    input [7:0] B,
    output EQ,
    output GT
);

    assign EQ = (A == B);
    assign GT = (A > B);

endmodule
