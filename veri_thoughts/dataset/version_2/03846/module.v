
module mux4to1 (
    //# {{data|Data Signals}}
    input  A,
    input  B,
    input  C,
    input  D,
    output reg X, // Changed from wire to reg

    //# {{control|Control Signals}}
    input  S0,
    input  S1
);

    always @(*) begin
        if (S1 == 0 && S0 == 0) begin
            X = A;
        end else if (S1 == 0 && S0 == 1) begin
            X = B;
        end else if (S1 == 1 && S0 == 0) begin
            X = C;
        end else if (S1 == 1 && S0 == 1) begin
            X = D;
        end
    end

endmodule
