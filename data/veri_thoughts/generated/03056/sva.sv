module top_module_sva(
    input logic [31:0] a,
    input logic [31:0] b,
    input logic        enable,
    input logic [31:0] out
);

    function automatic logic carry_prefix(
        input logic [31:0] a_i,
        input logic [31:0] b_i,
        input integer      idx
    );
        logic [31:0] g_i;
        logic [31:0] p_i;
        logic        carry_val;
        integer      j;
        begin
            g_i = a_i & b_i;
            p_i = a_i | b_i;
            carry_val = g_i[0];
            if (idx == 0) begin
                carry_prefix = carry_val;
            end else begin
                for (j = 1; j <= idx; j = j + 1) begin
                    carry_val = g_i[j] | (p_i[j] & carry_val);
                end
                carry_prefix = carry_val;
            end
        end
    endfunction

    // Disabling the control logic forces the top-level output low.
    check_disable_forces_zero: assert property (
        @($global_clock) !enable |-> (out == 32'h00000000)
    );

    // A zero operand produces a zero enabled result.
    check_zero_operand_yields_zero: assert property (
        @($global_clock) enable && ((a == 32'h00000000) || (b == 32'h00000000)) |-> (out == 32'h00000000)
    );

    // The least-significant bit matches the base assignment when enabled.
    check_enabled_lsb_base_case: assert property (
        @($global_clock) enable |-> (out[0] == (a[0] & b[0]))
    );

    generate
        genvar i;
        for (i = 1; i < 32; i = i + 1) begin : gen_recursive_output_bit_checks
            // Each higher bit follows the recursive carry-based expression when enabled.
            check_enabled_recursive_output_bit: assert property (
                @($global_clock) enable |-> (
                    out[i] == ((a[i] & b[i]) ^ ((a[i] | b[i]) & carry_prefix(a, b, i-1)))
                )
            );
        end
    endgenerate

endmodule