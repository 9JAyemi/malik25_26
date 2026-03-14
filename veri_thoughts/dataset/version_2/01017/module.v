module tornado_epcs_flash_controller_0_atom (
    // inputs:
    dclkin,
    oe,
    scein,
    sdoin,
    // outputs:
    data0out
);

    output data0out;
    input dclkin;
    input oe;
    input scein;
    input sdoin;

    wire data0out;

    assign data0out = sdoin | scein | dclkin | oe;

endmodule