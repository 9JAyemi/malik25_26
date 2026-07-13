module or1200_mem2reg_sva (
    input logic [1:0]  addr,
    input logic [3:0]  lsu_op,
    input logic [31:0] memdata,
    input logic [31:0] regdata
);

    // regdata always matches the implemented LSU-to-register mapping.
    check_complete_regdata_mapping: assert property (
        @($global_clock)
        regdata == ((lsu_op == 4'b0010) ? {{24{memdata[7]}}, memdata[7:0]} :
                   (lsu_op == 4'b0011) ? {{16{memdata[15]}}, memdata[15:0]} :
                                         memdata)
    );

    // Byte-load opcode sign-extends memdata[7:0].
    check_lb_sign_extend: assert property (
        @($global_clock)
        (lsu_op == 4'b0010) |-> (regdata == {{24{memdata[7]}}, memdata[7:0]})
    );

    // Halfword-load opcode sign-extends memdata[15:0].
    check_lh_sign_extend: assert property (
        @($global_clock)
        (lsu_op == 4'b0011) |-> (regdata == {{16{memdata[15]}}, memdata[15:0]})
    );

    // Word-load opcode passes memdata through.
    check_lw_passthrough: assert property (
        @($global_clock)
        (lsu_op == 4'b0100) |-> (regdata == memdata)
    );

    // All other opcodes pass memdata through.
    check_default_passthrough: assert property (
        @($global_clock)
        ((lsu_op != 4'b0010) && (lsu_op != 4'b0011) && (lsu_op != 4'b0100)) |-> (regdata == memdata)
    );

    // Changing only addr does not affect regdata.
    check_addr_has_no_effect: assert property (
        @($global_clock)
        ($changed(addr) && $stable(lsu_op) && $stable(memdata)) |-> $stable(regdata)
    );

    // Stable opcode and memory data keep regdata stable.
    check_stable_inputs_hold_output: assert property (
        @($global_clock)
        ($stable(lsu_op) && $stable(memdata)) |-> $stable(regdata)
    );

endmodule