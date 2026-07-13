
module my_module (
    input  in1 ,
    input  in2 ,
    input  in3 ,
    input  in4 ,
    input  in5 ,
    input  in6 ,
    input  in7 ,
    input  in8 ,
    input c1,
    input b1,
    input a2,
    input a1,
    output out1
);
    assign out1 = a1 & a2 & b1 & c1;

endmodule