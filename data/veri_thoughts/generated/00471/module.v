
module mux4to1_enable (
    input [3:0] in,
    input en,
    output out
);

    assign out = en ? in[0] : ( en ? in[1] : ( en ? in[2] :  in[3] ) );

endmodule