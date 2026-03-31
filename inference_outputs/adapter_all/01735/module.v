
module tri_buf (
    inout wire A,
    output wire Z,
    input wire TE_B
);

    assign Z = (TE_B) ? 1'b0 : A;

endmodule