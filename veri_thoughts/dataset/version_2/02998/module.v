module generate_HI_LO (
    HI,
    LO,
    pullup0_out,
    pulldown0_out,
    pwrgood_pp
);

    output HI;
    output LO;
    input pullup0_out;
    input pulldown0_out;
    input pwrgood_pp;

    assign HI = pwrgood_pp & pullup0_out;
    assign LO = ~pwrgood_pp & ~pulldown0_out;

endmodule