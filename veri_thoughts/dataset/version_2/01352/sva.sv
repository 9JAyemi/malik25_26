module binary_to_gray_sva (
    input logic [3:0] in,
    input logic       load,
    input logic [3:0] out,
    input logic       valid
);

    ///// Update behavior on load /////
    // On the next load edge, out equals Gray(in) captured at the previous load edge.
    check_out_gray_next: assert property (
        @(posedge load) 1'b1 |=> (out == $past((in >> 1) ^ in))
    );

    // On the next load edge, out[3] mirrors previous in[3].
    check_out_bit3_next: assert property (
        @(posedge load) 1'b1 |=> (out[3] == $past(in[3]))
    );

    // On the next load edge, out[2] equals previous in[3]^in[2].
    check_out_bit2_next: assert property (
        @(posedge load) 1'b1 |=> (out[2] == ($past(in[3]) ^ $past(in[2])))
    );

    // On the next load edge, out[1] equals previous in[2]^in[1].
    check_out_bit1_next: assert property (
        @(posedge load) 1'b1 |=> (out[1] == ($past(in[2]) ^ $past(in[1])))
    );

    // On the next load edge, out[0] equals previous in[1]^in[0].
    check_out_bit0_next: assert property (
        @(posedge load) 1'b1 |=> (out[0] == ($past(in[1]) ^ $past(in[0])))
    );

    ///// Valid behavior /////
    // On the next load edge, valid must be 1 (since it is set to 1 on every load).
    check_valid_set_next: assert property (
        @(posedge load) 1'b1 |=> (valid == 1'b1)
    );

    // If valid was 1 at the previous load edge, it remains 1 at this load edge.
    check_valid_sticky_across_edges: assert property (
        @(posedge load) $past(valid) |-> (valid == 1'b1)
    );

    ///// Consistency across consecutive load edges /////
    // If in is unchanged across two consecutive load edges, out is unchanged at the second edge.
    check_out_stable_when_in_stable: assert property (
        @(posedge load) ($past(in) == $past(in,2)) |-> (out == $past(out))
    );

    // If in changed between the last two load edges, out changes accordingly at the current edge.
    check_out_changes_when_in_changes: assert property (
        @(posedge load) ($past(in) != $past(in,2)) |-> (out != $past(out))
    );

endmodule