module dffsre(
    output reg Q,
    input D,
    input C,
    input E,
    input R,
    input S
);
    parameter [0:0] INIT = 1'b0;
    initial Q = INIT;
    always @(posedge C) begin
        if (E) begin
            if (S)
                Q <= 1'b1;
            else if (R)
                Q <= 1'b0;
            else
                Q <= D;
        end
    end
endmodule