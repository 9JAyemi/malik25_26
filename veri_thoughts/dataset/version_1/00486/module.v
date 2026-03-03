
module my_module (
    input A1,
    input A2,
    input A3,
    input A4,
    input B1,
    output X
);

    reg X_A, X_B;

    always @(*) begin
        if (A1 == 1) begin
            X_A = A2;
        end else begin
            X_A = A3 ^ A4;
        end
    end

    always @(*) begin
        if (B1 == 1) begin
            X_B = ~X_A;
        end else begin
            X_B = X_A;
        end
    end
    
    assign X = X_B;

endmodule