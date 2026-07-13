
module my_module (
    input  A1,
    input  A2,
    input  A3,
    input  A4,
    input  B1,
    output reg X
);

    wire X_w;

    always @(*) begin
        if (A1 == A2 && A3 == A4) begin
            X = B1;
        end else begin
            X = A1 & A2;
        end
    end

endmodule