module jt12_eg_final_sva (
    input logic [6:0] lfo_mod,
    input logic       amsen,
    input logic [1:0] ams,
    input logic [6:0] tl,
    input logic [9:0] eg_pure_in,
    input logic       ssg_inv,
    input logic [9:0] eg_limited
);

    function automatic logic [5:0] calc_am_inverted(
        input logic [6:0] lfo_mod_i
    );
    begin
        calc_am_inverted = lfo_mod_i[6] ? ~lfo_mod_i[5:0] : lfo_mod_i[5:0];
    end
    endfunction

    function automatic logic [8:0] calc_am_final(
        input logic [6:0] lfo_mod_i,
        input logic       amsen_i,
        input logic [1:0] ams_i
    );
        logic [5:0] am_inv;
    begin
        am_inv = calc_am_inverted(lfo_mod_i);
        casez ({amsen_i, ams_i})
            3'b1_01: calc_am_final = {5'd0, am_inv[5:2]};
            3'b1_10: calc_am_final = {3'd0, am_inv};
            3'b1_11: calc_am_final = {2'd0, am_inv, 1'b0};
            default: calc_am_final = 9'd0;
        endcase
    end
    endfunction

    function automatic logic [9:0] calc_eg_pream(
        input logic       ssg_inv_i,
        input logic [9:0] eg_pure_in_i
    );
    begin
        calc_eg_pream = ssg_inv_i ? (10'h200 - eg_pure_in_i) : eg_pure_in_i;
    end
    endfunction

    function automatic logic [11:0] calc_sum_no_am(
        input logic [6:0] tl_i,
        input logic       ssg_inv_i,
        input logic [9:0] eg_pure_in_i
    );
    begin
        calc_sum_no_am = {1'b0, tl_i, 3'd0} + {1'b0, calc_eg_pream(ssg_inv_i, eg_pure_in_i)};
    end
    endfunction

    function automatic logic [11:0] calc_sum_with_am(
        input logic [6:0] tl_i,
        input logic       ssg_inv_i,
        input logic [9:0] eg_pure_in_i,
        input logic [8:0] am_val_i
    );
        logic [11:0] sum_no_am_v;
    begin
        sum_no_am_v = calc_sum_no_am(tl_i, ssg_inv_i, eg_pure_in_i);
        calc_sum_with_am = sum_no_am_v + {3'd0, am_val_i};
    end
    endfunction

    function automatic logic [11:0] calc_sum_full(
        input logic [6:0] lfo_mod_i,
        input logic       amsen_i,
        input logic [1:0] ams_i,
        input logic [6:0] tl_i,
        input logic [9:0] eg_pure_in_i,
        input logic       ssg_inv_i
    );
    begin
        calc_sum_full = calc_sum_with_am(
            tl_i,
            ssg_inv_i,
            eg_pure_in_i,
            calc_am_final(lfo_mod_i, amsen_i, ams_i)
        );
    end
    endfunction

    function automatic logic [9:0] calc_limit(
        input logic [11:0] sum_i
    );
    begin
        calc_limit = (sum_i[11:10] == 2'd0) ? sum_i[9:0] : 10'h3ff;
    end
    endfunction

    function automatic logic [9:0] calc_eg_limited(
        input logic [6:0] lfo_mod_i,
        input logic       amsen_i,
        input logic [1:0] ams_i,
        input logic [6:0] tl_i,
        input logic [9:0] eg_pure_in_i,
        input logic       ssg_inv_i
    );
    begin
        calc_eg_limited = calc_limit(
            calc_sum_full(lfo_mod_i, amsen_i, ams_i, tl_i, eg_pure_in_i, ssg_inv_i)
        );
    end
    endfunction

    function automatic logic [9:0] calc_eg_limited_no_am(
        input logic [6:0] tl_i,
        input logic       ssg_inv_i,
        input logic [9:0] eg_pure_in_i
    );
    begin
        calc_eg_limited_no_am = calc_limit(calc_sum_no_am(tl_i, ssg_inv_i, eg_pure_in_i));
    end
    endfunction

    function automatic logic [9:0] calc_eg_limited_with_am(
        input logic [6:0] tl_i,
        input logic       ssg_inv_i,
        input logic [9:0] eg_pure_in_i,
        input logic [8:0] am_val_i
    );
    begin
        calc_eg_limited_with_am = calc_limit(calc_sum_with_am(tl_i, ssg_inv_i, eg_pure_in_i, am_val_i));
    end
    endfunction

    // Output matches the full combinational transfer function.
    check_full_transfer_function: assert property (
        @($global_clock)
        eg_limited == calc_eg_limited(lfo_mod, amsen, ams, tl, eg_pure_in, ssg_inv)
    );

    // Disabled AM contributes zero modulation.
    check_am_disabled_zero_contribution: assert property (
        @($global_clock)
        (!amsen) |-> (eg_limited == calc_eg_limited_no_am(tl, ssg_inv, eg_pure_in))
    );

    // AMS value 00 also contributes zero modulation.
    check_ams_zero_zero_contribution: assert property (
        @($global_clock)
        (amsen && (ams == 2'b00)) |-> (eg_limited == calc_eg_limited_no_am(tl, ssg_inv, eg_pure_in))
    );

    // AMS 01 uses the reduced AM contribution.
    check_ams_one_reduced_am: assert property (
        @($global_clock)
        (amsen && (ams == 2'b01)) |-> (
            eg_limited == calc_eg_limited_with_am(
                tl,
                ssg_inv,
                eg_pure_in,
                calc_am_final(lfo_mod, 1'b1, 2'b01)
            )
        )
    );

    // AMS 10 uses the full AM contribution.
    check_ams_two_full_am: assert property (
        @($global_clock)
        (amsen && (ams == 2'b10)) |-> (
            eg_limited == calc_eg_limited_with_am(
                tl,
                ssg_inv,
                eg_pure_in,
                calc_am_final(lfo_mod, 1'b1, 2'b10)
            )
        )
    );

    // AMS 11 uses the doubled AM contribution.
    check_ams_three_doubled_am: assert property (
        @($global_clock)
        (amsen && (ams == 2'b11)) |-> (
            eg_limited == calc_eg_limited_with_am(
                tl,
                ssg_inv,
                eg_pure_in,
                calc_am_final(lfo_mod, 1'b1, 2'b11)
            )
        )
    );

    // Without SSG inversion and without AM, eg_pure_in is used directly.
    check_ssg_passthrough_without_am: assert property (
        @($global_clock)
        ((!ssg_inv) && (!amsen || (ams == 2'b00))) |-> (
            eg_limited == calc_eg_limited_no_am(tl, 1'b0, eg_pure_in)
        )
    );

    // With SSG inversion and without AM, 0x200-eg_pure_in is used.
    check_ssg_inversion_without_am: assert property (
        @($global_clock)
        (ssg_inv && (!amsen || (ams == 2'b00))) |-> (
            eg_limited == calc_eg_limited_no_am(tl, 1'b1, eg_pure_in)
        )
    );

    // Non-overflowing sums pass through their low 10 bits.
    check_unsaturated_passthrough: assert property (
        @($global_clock)
        (calc_sum_full(lfo_mod, amsen, ams, tl, eg_pure_in, ssg_inv)[11:10] == 2'd0) |-> (
            eg_limited == calc_sum_full(lfo_mod, amsen, ams, tl, eg_pure_in, ssg_inv)[9:0]
        )
    );

    // Overflowing sums saturate to the maximum output value.
    check_saturates_to_max: assert property (
        @($global_clock)
        (calc_sum_full(lfo_mod, amsen, ams, tl, eg_pure_in, ssg_inv)[11:10] != 2'd0) |-> (
            eg_limited == 10'h3ff
        )
    );

endmodule