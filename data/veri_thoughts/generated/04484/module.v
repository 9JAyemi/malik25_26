
module DFF_EN (
    input C, 
    input E, 
    input S, 
    input R, 
    input D,
    output reg Q
);

always @ (posedge C)
begin
    if (R)
        Q <= 1'b0;
    else if (S)
        Q <= 1'b1;
    else if (E == 1)
        Q <= D;
end

endmodule
module DFFSR (
    input C, 
    input S, 
    input R, 
    input D,
    output reg Q
);

always @ (posedge C)
begin
    if (R)
        Q <= 1'b0;
    else if (S)
        Q <= 1'b1;
    else
        Q <= D;
end

endmodule