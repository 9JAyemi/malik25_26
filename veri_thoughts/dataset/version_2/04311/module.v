
module mux4to1 (
    in0,
    in1,
    in2,
    in3,
    sel0,
    sel1,
    out
);

    input [3:0] in0, in1, in2, in3;
    input sel0, sel1;
    output [3:0] out;

    wire [3:0] sel;

    assign sel = {sel1, sel0};

    assign out = (sel == 2'b00) ? in0 :
                 (sel == 2'b01) ? in1 :
                 (sel == 2'b10) ? in2 :
                 in3;

endmodule
