module logic_module (
    input A1,
    input A2,
    input B1,
    input C1,
    output reg X
);

    // Local signals
    wire or0_out;
    wire and0_out_X;

    // Instantiation of gates
    or or0 (or0_out, A2, A1);
    and and0 (and0_out_X, or0_out, B1, C1);

    always @* begin
        X = and0_out_X;
    end

endmodule