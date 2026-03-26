module func (
    input A,
    input B,
    input C,
    output reg X
);

    always @(A, B, C)
    begin
        if (A && B && C)
            X = 1;
        else
             X = 0;
    end

endmodule