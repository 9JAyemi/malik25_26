module DAC_8BIT (
    input wire d0,
    input wire d1,
    input wire d2,
    input wire d3,
    input wire d4,
    input wire d5,
    input wire d6,
    input wire d7,
    output wire out_v
);

    assign out_v = d0 | d1 | d2 | d3 | d4 | d5 | d6 | d7 ;

endmodule