
module logic_gate (
    X ,
    A1,
    A2,
    A3,
    B1
);

    output X ;
    input  A1;
    input  A2;
    input  A3;
    input  B1;

    // Voltage supply signals
    supply1 VPWR;
    supply0 VGND;

    // Instantiate the 3-input AND gate
    and (
        X,
        A1,
        A2,
        A3,
        B1
    );

endmodule