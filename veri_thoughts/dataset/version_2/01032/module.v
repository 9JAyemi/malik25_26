
module logic_module (
    // module ports
    input A1,
    input A2,
    input B1,
    input B2,
    output X
);

    // Local signals
    wire and0_out ;
    wire and1_out ;
    wire or0_out;

    //  Name  Output     Other arguments
    and and0 (and0_out , B1, B2            );
    and and1 (and1_out , A1, A2            );
    or  or0  (or0_out  , and1_out, and0_out);
    assign X = or0_out;

endmodule
