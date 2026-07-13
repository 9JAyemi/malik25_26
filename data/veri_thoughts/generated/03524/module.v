module mux_4to1 (
    input in0,
    input in1,
    input in2,
    input in3,
    input sel1,
    input sel0,
    output reg out
);

    wire not_sel1;
    wire not_sel0;
    wire and1;
    wire and2;
    wire and3;
    wire and4;
    wire or1;

    // Invert select wires
    assign not_sel1 = ~sel1;
    assign not_sel0 = ~sel0;

    // AND gates to create all possible combinations
    assign and1 = in0 & not_sel1 & not_sel0;
    assign and2 = in1 & not_sel1 & sel0;
    assign and3 = in2 & sel1 & not_sel0;
    assign and4 = in3 & sel1 & sel0;

    // OR gates to combine the AND gates
    assign or1 = and1 | and2 | and3 | and4;

    // Output
    always @* begin
        out = or1;
    end

endmodule