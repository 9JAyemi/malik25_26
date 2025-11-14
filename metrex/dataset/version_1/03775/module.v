
module mult_srst_ena (
    input  wire        CLK,
    input  wire        RST,
    input  wire        ENA,
    input  wire [ 8:0] A,
    input  wire [ 8:0] B,
    output wire [17:0] Z
);

    reg [8:0] ra;
    always @(posedge CLK)
        if (RST)      ra <= 0;
        else if (ENA) ra <= A;

    MULT9X9 mult (
        .A (ra),
        .B (B),
        .Z (Z)
    );

endmodule
module MULT9X9 (
    input  wire [8:0] A,
    input  wire [8:0] B,
    output wire [17:0] Z
);

    wire [17:0] mult_out;
    assign mult_out = A * B;

    assign Z = mult_out;

endmodule