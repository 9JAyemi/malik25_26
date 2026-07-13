module top_module_sva (
    input logic [3:0] in,
    input logic [1:0] ctrl,
    input logic [5:0] out
);

    function automatic logic [3:0] calc_shifted (
        input logic [3:0] in_f,
        input logic [1:0] ctrl_f
    );
        begin
            case (ctrl_f)
                2'b00: calc_shifted = in_f << 1;
                2'b01: calc_shifted = in_f << 2;
                2'b10: calc_shifted = in_f << 3;
                default: calc_shifted = in_f << 4;
            endcase
        end
    endfunction

    function automatic logic [3:0] calc_one_count (
        input logic [3:0] shifted_f
    );
        int idx;
        begin
            calc_one_count = 4'd0;
            for (idx = 0; idx < 4; idx = idx + 1) begin
                if (shifted_f[idx] == 1'b1) begin
                    calc_one_count = calc_one_count + 4'd1;
                end
            end
        end
    endfunction

    function automatic logic [5:0] calc_out (
        input logic [3:0] in_f,
        input logic [1:0] ctrl_f
    );
        logic [3:0] shifted_f;
        logic [3:0] one_count_f;
        begin
            shifted_f   = calc_shifted(in_f, ctrl_f);
            one_count_f = calc_one_count(shifted_f);
            calc_out    = {2'b00, (shifted_f + one_count_f)};
        end
    endfunction

    // No RTL clock or reset; sample the combinational logic on $global_clock.

    // The output must match the RTL's full shift, count, and add function.
    check_full_function: assert property (
        @($global_clock) disable iff (1'b0)
        out == calc_out(in, ctrl)
    );

    // ctrl=00 shifts left by 1 before counting ones and adding.
    check_shift_by1: assert property (
        @($global_clock) disable iff (1'b0)
        (ctrl == 2'b00) |-> (out == {2'b00, ((in << 1) + calc_one_count(in << 1))})
    );

    // ctrl=01 shifts left by 2 before counting ones and adding.
    check_shift_by2: assert property (
        @($global_clock) disable iff (1'b0)
        (ctrl == 2'b01) |-> (out == {2'b00, ((in << 2) + calc_one_count(in << 2))})
    );

    // ctrl=10 shifts left by 3 before counting ones and adding.
    check_shift_by3: assert property (
        @($global_clock) disable iff (1'b0)
        (ctrl == 2'b10) |-> (out == {2'b00, ((in << 3) + calc_one_count(in << 3))})
    );

    // ctrl=11 shifts a 4-bit value left by 4, which forces the output to zero.
    check_shift_by4_zero: assert property (
        @($global_clock) disable iff (1'b0)
        (ctrl == 2'b11) |-> (out == 6'd0)
    );

    // The 4-bit addition result is zero-extended into the 6-bit output.
    check_output_zero_extended: assert property (
        @($global_clock) disable iff (1'b0)
        out[5:4] == 2'b00
    );

    // A zero input must produce a zero output for every control value.
    check_zero_input_zero_output: assert property (
        @($global_clock) disable iff (1'b0)
        (in == 4'b0000) |-> (out == 6'd0)
    );

endmodule