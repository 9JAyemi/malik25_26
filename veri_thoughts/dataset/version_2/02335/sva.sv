module top_module_sva (
    input  logic CLK,
    input  logic [2:0] vec,
    input  logic a,
    input  logic b,
    input  logic cin,
    input  logic select,
    input  logic cout,
    input  logic [3:0] outv
);
    ///// Position decode reflected on outv[3:1] /////
    // outv[3:1] must match {vec==3'b010, vec==3'b001, vec==3'b000}.
    check_outv_decode_map: assert property (
        @(posedge CLK) disable iff (1'b0) outv[3:1] == { (vec == 3'b010), (vec == 3'b001), (vec == 3'b000) }
    );
    // outv[3:1] is one-hot or all-zero.
    check_outv_decode_onehot0: assert property (
        @(posedge CLK) disable iff (1'b0) $onehot0(outv[3:1])
    );
    // If outv[3] is HIGH then vec must be 3'b010.
    check_outv3_implies_vec010: assert property (
        @(posedge CLK) disable iff (1'b0) outv[3] |-> (vec == 3'b010)
    );
    // If outv[2] is HIGH then vec must be 3'b001.
    check_outv2_implies_vec001: assert property (
        @(posedge CLK) disable iff (1'b0) outv[2] |-> (vec == 3'b001)
    );
    // If outv[1] is HIGH then vec must be 3'b000.
    check_outv1_implies_vec000: assert property (
        @(posedge CLK) disable iff (1'b0) outv[1] |-> (vec == 3'b000)
    );
    // For vec not in {000,001,010}, outv[3:1] must be 3'b000.
    check_vec_other_yields_zero_decode: assert property (
        @(posedge CLK) disable iff (1'b0) (!(vec inside {3'b000,3'b001,3'b010})) |-> (outv[3:1] == 3'b000)
    );

    ///// Full adder behavior on cout and outv[0] /////
    // outv[0] equals a ^ b ^ cin.
    check_sum_is_xor: assert property (
        @(posedge CLK) disable iff (1'b0) outv[0] == (a ^ b ^ cin)
    );
    // cout equals majority of (a,b,cin).
    check_cout_is_majority: assert property (
        @(posedge CLK) disable iff (1'b0) cout == ((a & b) | (a & cin) | (b & cin))
    );

    ///// Independence from 'select' (unused by functional outputs) /////
    // Rising select alone does not change outv or cout.
    check_select_rise_no_effect: assert property (
        @(posedge CLK) disable iff (1'b0) ($rose(select) && $stable({vec,a,b,cin})) |-> $stable({outv, cout})
    );
    // Falling select alone does not change outv or cout.
    check_select_fall_no_effect: assert property (
        @(posedge CLK) disable iff (1'b0) ($fell(select) && $stable({vec,a,b,cin})) |-> $stable({outv, cout})
    );

    ///// Independence partitions between vec and adder inputs /////
    // Changing vec alone does not change cout.
    check_cout_independent_of_vec: assert property (
        @(posedge CLK) disable iff (1'b0)
            (($rose(vec[0]) || $fell(vec[0]) || $rose(vec[1]) || $fell(vec[1]) || $rose(vec[2]) || $fell(vec[2])) && $stable({a,b,cin,select}))
            |-> $stable(cout)
    );
    // Changing a/b/cin alone does not change outv[3:1].
    check_decode_independent_of_adder_inputs: assert property (
        @(posedge CLK) disable iff (1'b0)
            ($stable(vec) && ($rose(a) || $fell(a) || $rose(b) || $fell(b) || $rose(cin) || $fell(cin)))
            |-> $stable(outv[3:1])
    );
    // Changing vec/select alone does not change outv[0].
    check_outv0_independent_of_vec_and_select: assert property (
        @(posedge CLK) disable iff (1'b0)
            ((($rose(vec[0]) || $fell(vec[0]) || $rose(vec[1]) || $fell(vec[1]) || $rose(vec[2]) || $fell(vec[2])) || $rose(select) || $fell(select)) && $stable({a,b,cin}))
            |-> $stable(outv[0])
    );
endmodule