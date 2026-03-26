module muxMUL_sva (
    input logic [3:0] ia,
    input logic [3:0] ib,
    input logic [7:0] o
);

    function automatic [7:0] partial_product (
        input logic [3:0] a,
        input logic [1:0] sel
    );
        begin
            case (sel)
                2'b00: partial_product = 8'b0;
                2'b01: partial_product = {4'b0, a};
                2'b10: partial_product = {4'b0, (a << 1)};
                2'b11: partial_product = {4'b0, (a << 1)} + {4'b0, a};
            endcase
        end
    endfunction

    // Output equals the lower partial product plus the shifted upper partial product.
    check_output_matches_selected_partials: assert property (
        @($global_clock)
        o == (partial_product(ia, ib[1:0]) + (partial_product(ia, ib[3:2]) << 2))
    );

    // A zero multiplier produces a zero output.
    check_zero_multiplier_outputs_zero: assert property (
        @($global_clock)
        (ib == 4'b0000) |-> (o == 8'b0)
    );

    // A zero multiplicand produces a zero output.
    check_zero_multiplicand_outputs_zero: assert property (
        @($global_clock)
        (ia == 4'b0000) |-> (o == 8'b0)
    );

    // When the upper selector is 00, only the lower partial product contributes.
    check_upper_zero_uses_only_lower_partial: assert property (
        @($global_clock)
        (ib[3:2] == 2'b00) |-> (o == partial_product(ia, ib[1:0]))
    );

    // When the lower selector is 00, only the shifted upper partial product contributes.
    check_lower_zero_uses_only_shifted_upper_partial: assert property (
        @($global_clock)
        (ib[1:0] == 2'b00) |-> (o == (partial_product(ia, ib[3:2]) << 2))
    );

    // Lower selector 01 passes the zero-extended ia value when upper selector is 00.
    check_lower_sel_one_path: assert property (
        @($global_clock)
        ((ib[3:2] == 2'b00) && (ib[1:0] == 2'b01)) |-> (o == {4'b0, ia})
    );

    // Lower selector 10 passes the truncated left shift of ia when upper selector is 00.
    check_lower_sel_two_path: assert property (
        @($global_clock)
        ((ib[3:2] == 2'b00) && (ib[1:0] == 2'b10)) |-> (o == {4'b0, (ia << 1)})
    );

    // Lower selector 11 passes the sum of ia and its truncated left shift when upper selector is 00.
    check_lower_sel_three_path: assert property (
        @($global_clock)
        ((ib[3:2] == 2'b00) && (ib[1:0] == 2'b11)) |-> (o == ({4'b0, (ia << 1)} + {4'b0, ia}))
    );

    // Upper selector 01 contributes the zero-extended ia value shifted left by two when lower selector is 00.
    check_upper_sel_one_path: assert property (
        @($global_clock)
        ((ib[1:0] == 2'b00) && (ib[3:2] == 2'b01)) |-> (o == ({4'b0, ia} << 2))
    );

    // Upper selector 10 contributes the truncated left shift of ia shifted left by two when lower selector is 00.
    check_upper_sel_two_path: assert property (
        @($global_clock)
        ((ib[1:0] == 2'b00) && (ib[3:2] == 2'b10)) |-> (o == ({4'b0, (ia << 1)} << 2))
    );

    // Upper selector 11 contributes the sum of ia and its truncated left shift, then shifts by two, when lower selector is 00.
    check_upper_sel_three_path: assert property (
        @($global_clock)
        ((ib[1:0] == 2'b00) && (ib[3:2] == 2'b11)) |-> (o == (({4'b0, (ia << 1)} + {4'b0, ia}) << 2))
    );

endmodule