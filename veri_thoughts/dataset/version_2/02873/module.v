
module mux_3to1_enable (
    input [3:0] a,
    input [3:0] b,
    input [3:0] c,
    input        en,
    input [1:0] sel,
    output [3:0] out
);

    wire        r;

    assign r = (en) ?
                 ((sel[1]) ? 1'b1 :
                  ((sel[0]) ? 1'b1 :
                               1'b0)) :
                 1'b0;

    assign out = (r) ? 
        ((sel[1]) ? a :
         ((sel[0]) ? b :
                     c)) : 4'b0;

endmodule