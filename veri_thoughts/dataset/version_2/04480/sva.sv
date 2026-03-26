module oh_mux_sva #(parameter DW = 1, parameter N = 1) (
    input logic [N-1:0]    sel,
    input logic [N*DW-1:0] in,
    input logic [DW-1:0]   out
);

    function automatic [DW-1:0] expected_out (
        input logic [N-1:0]    s,
        input logic [N*DW-1:0] d
    );
        integer k;
        begin
            expected_out = '0;
            for (k = 0; k < N; k = k + 1)
                expected_out = expected_out | ({DW{s[k]}} & d[((k+1)*DW-1)-:DW]);
        end
    endfunction

    // Output equals the OR of all selected input words.
    check_output_equation: assert property (
        @($global_clock) out == expected_out(sel, in)
    );

    // With no select bits set, the output is zero.
    check_no_select_zero: assert property (
        @($global_clock) (sel == '0) |-> (out == '0)
    );

    // A zero input bus forces a zero output.
    check_zero_input_zero_output: assert property (
        @($global_clock) (in == '0) |-> (out == '0)
    );

    // Stable inputs keep the output stable.
    check_stable_inputs_stable_output: assert property (
        @($global_clock) ($stable(sel) && $stable(in)) |-> $stable(out)
    );

    genvar i;
    generate
        for (i = 0; i < N; i = i + 1) begin : gen_onehot_checks
            // With only this select bit set, output matches this input word.
            check_onehot_select: assert property (
                @($global_clock) (sel[i] && $onehot(sel)) |-> (out == in[((i+1)*DW-1)-:DW])
            );
        end
    endgenerate

endmodule