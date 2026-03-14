module zet_next_or_not_sva (
    input  logic CLK,
    input  logic RESETn,
    input  logic [1:0] prefix,
    input  logic [7:1] opcode,
    input  logic cx_zero,
    input  logic zf,
    input  logic ext_int,
    input  logic next_in_opco,
    input  logic next_in_exec
);

    function automatic bit valid_ops_f (input logic [7:1] op);
        valid_ops_f = (op == 7'b1010_010) ||
                      (op == 7'b1010_011) ||
                      (op == 7'b1010_101) ||
                      (op == 7'b1010_110) ||
                      (op == 7'b1010_111);
    endfunction

    function automatic bit exit_z_f (input logic [1:0] pref, input logic [7:1] op, input logic zf_i);
        bit cmp_sca;
        cmp_sca = op[2] & op[1];
        exit_z_f = pref[0] ? (cmp_sca ? ~zf_i : 1'b0)
                           : (cmp_sca ?  zf_i : 1'b0);
    endfunction

    // next_in_opco equals prefix[1] && valid_ops && cx_zero.
    check_next_in_opco_definition: assert property (
        @(posedge CLK) disable iff (!RESETn)
        next_in_opco == (prefix[1] && valid_ops_f(opcode) && cx_zero)
    );

    // next_in_exec equals prefix[1] && valid_ops && !exit_rep && !ext_int.
    check_next_in_exec_definition: assert property (
        @(posedge CLK) disable iff (!RESETn)
        next_in_exec == (prefix[1] && valid_ops_f(opcode) && !(cx_zero | exit_z_f(prefix, opcode, zf)) && !ext_int)
    );

    // next_in_opco requires prefix[1].
    check_opco_requires_prefix1: assert property (
        @(posedge CLK) disable iff (!RESETn)
        next_in_opco |-> (prefix[1] == 1'b1)
    );

    // next_in_opco requires opcode to be valid.
    check_opco_requires_valid_ops: assert property (
        @(posedge CLK) disable iff (!RESETn)
        next_in_opco |-> valid_ops_f(opcode)
    );

    // next_in_opco requires cx_zero.
    check_opco_requires_cx_zero: assert property (
        @(posedge CLK) disable iff (!RESETn)
        next_in_opco |-> (cx_zero == 1'b1)
    );

    // next_in_exec requires prefix[1].
    check_exec_requires_prefix1: assert property (
        @(posedge CLK) disable iff (!RESETn)
        next_in_exec |-> (prefix[1] == 1'b1)
    );

    // next_in_exec requires opcode to be valid.
    check_exec_requires_valid_ops: assert property (
        @(posedge CLK) disable iff (!RESETn)
        next_in_exec |-> valid_ops_f(opcode)
    );

    // next_in_exec requires cx_zero LOW.
    check_exec_requires_not_cx_zero: assert property (
        @(posedge CLK) disable iff (!RESETn)
        next_in_exec |-> (cx_zero == 1'b0)
    );

    // next_in_exec requires ext_int LOW.
    check_exec_requires_not_ext_int: assert property (
        @(posedge CLK) disable iff (!RESETn)
        next_in_exec |-> (ext_int == 1'b0)
    );

    // next_in_exec requires exit_z LOW.
    check_exec_requires_not_exit_z: assert property (
        @(posedge CLK) disable iff (!RESETn)
        next_in_exec |-> (exit_z_f(prefix, opcode, zf) == 1'b0)
    );

    // If cmp_sca is 1, next_in_exec implies zf matches prefix[0] rule.
    check_exec_zf_when_cmp_sca: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (next_in_exec && (opcode[2] & opcode[1])) |-> (prefix[0] ? (zf == 1'b1) : (zf == 1'b0))
    );

    // Outputs cannot both be HIGH simultaneously.
    check_outputs_mutex: assert property (
        @(posedge CLK) disable iff (!RESETn)
        !(next_in_opco && next_in_exec)
    );

    // Invalid opcode forces both outputs LOW.
    check_invalid_ops_block_outputs: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (!valid_ops_f(opcode)) |-> (!next_in_opco && !next_in_exec)
    );

    // With prefix[1] && valid_ops && cx_zero, opco asserts and exec deasserts.
    check_cx_zero_selects_opco: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (prefix[1] && valid_ops_f(opcode) && cx_zero) |-> (next_in_opco && !next_in_exec)
    );

    // With all exec conditions met, exec asserts and opco deasserts.
    check_exec_true_when_conditions_met: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (prefix[1] && valid_ops_f(opcode) && !ext_int && !cx_zero &&
         ( !(opcode[2] & opcode[1]) || (prefix[0] ? (zf==1'b1) : (zf==1'b0)) )
        ) |-> (next_in_exec && !next_in_opco)
    );

    // ext_int HIGH blocks next_in_exec.
    check_ext_int_blocks_exec: assert property (
        @(posedge CLK) disable iff (!RESETn)
        ext_int |-> (next_in_exec == 1'b0)
    );

endmodule