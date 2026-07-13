
module dff(
    output reg Q,
    input D,
    input C,
    input E,
    input R,
    input S
);
    parameter INIT = 1'b0;

    always @(posedge C)
    begin
        if (!R)
            Q <= INIT;
        else if (!S)
            Q <= 1'b1;
        else if (E)
            Q <= D;
    end
endmodule