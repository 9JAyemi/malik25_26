module top_module_sva (
    input  logic [3:0] in,
    input  logic       out_add,
    input  logic       out_sub,
    input  logic       out_mul
);
    // out_add is LSB of (in + 1)
    check_out_add_is_lsb_of_in_plus_one: assert property (
        @(posedge $global_clock) out_add == ((in + 4'd1)[0])
    );

    // out_sub is LSB of (in - 1)
    check_out_sub_is_lsb_of_in_minus_one: assert property (
        @(posedge $global_clock) out_sub == ((in - 4'd1)[0])
    );

    // out_mul is LSB of (in * in)
    check_out_mul_is_lsb_of_square: assert property (
        @(posedge $global_clock) out_mul == ((in * in)[0])
    );

    // LSB of (in + 1) equals ~in[0]
    check_out_add_equals_not_in0: assert property (
        @(posedge $global_clock) out_add == ~in[0]
    );

    // LSB of (in - 1) equals ~in[0]
    check_out_sub_equals_not_in0: assert property (
        @(posedge $global_clock) out_sub == ~in[0]
    );

    // LSB of (in * in) equals in[0]
    check_out_mul_equals_in0: assert property (
        @(posedge $global_clock) out_mul == in[0]
    );

    // out_add and out_sub match
    check_add_and_sub_match: assert property (
        @(posedge $global_clock) out_add == out_sub
    );

    // out_mul is the inverse of out_add
    check_mul_is_inverse_of_add: assert property (
        @(posedge $global_clock) out_mul == ~out_add
    );

    // If in[0] is 0, then add/sub LSBs are 1 and mul LSB is 0
    check_outputs_when_in0_is_zero: assert property (
        @(posedge $global_clock) (in[0] == 1'b0) |-> (out_add == 1'b1) && (out_sub == 1'b1) && (out_mul == 1'b0)
    );

    // If in[0] is 1, then add/sub LSBs are 0 and mul LSB is 1
    check_outputs_when_in0_is_one: assert property (
        @(posedge $global_clock) (in[0] == 1'b1) |-> (out_add == 1'b0) && (out_sub == 1'b0) && (out_mul == 1'b1)
    );

    // With stable input, outputs remain stable (pure combinational)
    check_stability_with_stable_input: assert property (
        @(posedge $global_clock) $stable(in) |-> $stable(out_add) && $stable(out_sub) && $stable(out_mul)
    );
endmodule