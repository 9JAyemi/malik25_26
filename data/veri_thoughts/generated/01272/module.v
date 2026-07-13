
module my_module (
    X ,
    A1,
    A2,
    A3,
    A4,
    B1
);

    // Module ports
    output X ;
    input  A1;
    input  A2;
    input  A3;
    input  A4;
    input  B1;

    // Local signals
    wire and_out;
    wire temp_and;

    //  Name  Output     Other arguments
    and and1 (temp_and , A1, A2);
    and and2 (and_out , temp_and, A3, A4);
    or  or1  (X , and_out, B1);

endmodule