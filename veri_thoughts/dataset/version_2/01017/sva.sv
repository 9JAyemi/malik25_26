module tornado_epcs_flash_controller_0_atom_sva (
    input  logic dclkin,
    input  logic oe,
    input  logic scein,
    input  logic sdoin,
    input  logic data0out
);
    // Output is the bitwise OR of all inputs.
    check_or_function: assert property (
        @(posedge dclkin) data0out == (sdoin | scein | dclkin | oe)
    );

    // If sdoin is HIGH, data0out must be HIGH.
    check_sdoin_drives_out_high: assert property (
        @(posedge dclkin) sdoin |-> data0out
    );

    // If scein is HIGH, data0out must be HIGH.
    check_scein_drives_out_high: assert property (
        @(posedge dclkin) scein |-> data0out
    );

    // If oe is HIGH, data0out must be HIGH.
    check_oe_drives_out_high: assert property (
        @(posedge dclkin) oe |-> data0out
    );

    // On every posedge of dclkin, data0out must be HIGH (since dclkin contributes to the OR).
    check_dclkin_drives_out_high: assert property (
        @(posedge dclkin) data0out
    );
endmodule