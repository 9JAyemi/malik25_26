
module digital_circuit_module (
    output reg Y   ,
    input  A1  ,
    input  A2  ,
    input  B1_N,
    input  VPWR,
    input  VGND,
    input  VPB ,
    input  VNB
);

    wire Y1;
    wire Y2;
    wire c;

    assign Y1 = (A1 & A2 & B1_N);
    assign Y2 = ~(A1 & A2 & B1_N);
    assign c = ~VPWR;

    always @* begin
        Y = c ? Y2 : Y1;
    end

endmodule