
module and_gate (
    output Y ,
    input  A1,
    input  A2,
    input  B1,
    input  C1,
    input  D1
);


    wire w1, w2, w3;
    and (
        w1,
        A1,
        A2
    );
    and (
        w2,
        w1,
        B1
    );
    and (
        w3,
        w2,
        C1
    );
    and (
        Y,
        w3,
        D1
    );

endmodule