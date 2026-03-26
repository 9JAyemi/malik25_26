module zet_next_or_not_sva (
    input logic [1:0] prefix,
    input logic [7:1] opcode,
    input logic cx_zero,
    input logic zf,
    input logic ext_int,
    input logic next_in_opco,
    input logic next_in_exec,
    input logic use_eintp
);

    wire cmp_sca;
    wire exit_z;
    wire exit_rep;
    wire valid_ops;

    assign cmp_sca  = opcode[7] & opcode[2] & opcode[1];
    assign exit_z   = prefix[0] ? (cmp_sca ? ~zf : 1'b0)
                                : (cmp_sca ?  zf : 1'b0);
    assign exit_rep = cx_zero | exit_z;
    assign valid_ops = (opcode[7:1] == 7'b1010_010) ||
                       (opcode[7:1] == 7'b1010_011) ||
                       (opcode[7:1] == 7'b1010_101) ||
                       (opcode[7:1] == 7'b0110_110) ||
                       (opcode[7:1] == 7'b0110_111) ||
                       (opcode[7:1] == 7'b1010_110) ||
                       (opcode[7:1] == 7'b1010_111);

    // Purely combinational DUT; sample on the formal global clock.

    // next_in_exec must match its combinational definition.
    check_next_in_exec_definition: assert property (
        @($global_clock) disable iff (1'b0)
        next_in_exec == (prefix[1] && valid_ops && !exit_rep && !ext_int)
    );

    // next_in_opco must match its combinational definition.
    check_next_in_opco_definition: assert property (
        @($global_clock) disable iff (1'b0)
        next_in_opco == (prefix[1] && valid_ops && cx_zero)
    );

    // use_eintp must match its combinational definition.
    check_use_eintp_definition: assert property (
        @($global_clock) disable iff (1'b0)
        use_eintp == (prefix[1] && valid_ops && !exit_z)
    );

    // Without prefix[1], all outputs must be low.
    check_outputs_low_without_prefix1: assert property (
        @($global_clock) disable iff (1'b0)
        !prefix[1] |-> (!next_in_exec && !next_in_opco && !use_eintp)
    );

    // Invalid opcodes must not assert any output.
    check_outputs_low_for_invalid_opcode: assert property (
        @($global_clock) disable iff (1'b0)
        !valid_ops |-> (!next_in_exec && !next_in_opco && !use_eintp)
    );

    // cx_zero always blocks next_in_exec through exit_rep.
    check_cx_zero_blocks_exec: assert property (
        @($global_clock) disable iff (1'b0)
        cx_zero |-> !next_in_exec
    );

    // ext_int always blocks next_in_exec.
    check_ext_int_blocks_exec: assert property (
        @($global_clock) disable iff (1'b0)
        ext_int |-> !next_in_exec
    );

    // next_in_exec implies use_eintp is also asserted.
    check_exec_implies_use_eintp: assert property (
        @($global_clock) disable iff (1'b0)
        next_in_exec |-> use_eintp
    );

    // next_in_exec and next_in_opco cannot be high together.
    check_exec_opco_mutex: assert property (
        @($global_clock) disable iff (1'b0)
        !(next_in_exec && next_in_opco)
    );

    // When cmp_sca is low, use_eintp depends only on prefix[1] and valid_ops.
    check_use_eintp_when_not_cmp_sca: assert property (
        @($global_clock) disable iff (1'b0)
        !cmp_sca |-> (use_eintp == (prefix[1] && valid_ops))
    );

endmodule