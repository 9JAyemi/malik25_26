module mux4_2 (
    output reg X,
    input A0, A1, A2, A3, S0, S1, VPWR, VGND, VPB, VNB
);

    reg [3:0] A;
    reg [1:0] S;

    always @* begin
        A[0] = A0;
        A[1] = A1;
        A[2] = A2;
        A[3] = A3;

        S[0] = S0;
        S[1] = S1;

        case ({S[1], S[0]})
            2'b00: X = A[0];
            2'b01: X = A[1];
            2'b10: X = A[2];
            2'b11: X = A[3];
        endcase
    end

endmodule