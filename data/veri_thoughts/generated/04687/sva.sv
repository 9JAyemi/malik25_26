module top_module_sva (
    input logic [15:0] in0,
    input logic [15:0] in1,
    input logic control,
    input logic [1:0] OUT,
    input logic [15:0] addsub_out,
    input logic [3:0] comp_out
);

    // addsub_out follows the selected add/sub operation.
    check_addsub_function: assert property (
        @($global_clock) disable iff (1'b0)
        addsub_out == (control ? (in0 + in1) : (in0 - in1))
    );

    // Comparator reports greater when addsub_out low nibble exceeds in0 low nibble.
    check_comp_gt: assert property (
        @($global_clock) disable iff (1'b0)
        (addsub_out[3:0] > in0[3:0]) |-> (comp_out == 4'b0001)
    );

    // Comparator reports less when addsub_out low nibble is below in0 low nibble.
    check_comp_lt: assert property (
        @($global_clock) disable iff (1'b0)
        (addsub_out[3:0] < in0[3:0]) |-> (comp_out == 4'b0010)
    );

    // Comparator reports equal when the compared low nibbles match.
    check_comp_eq: assert property (
        @($global_clock) disable iff (1'b0)
        (addsub_out[3:0] == in0[3:0]) |-> (comp_out == 4'b0111)
    );

    // Comparator output is restricted to the implemented encodings.
    check_comp_valid_codes: assert property (
        @($global_clock) disable iff (1'b0)
        (comp_out == 4'b0001) || (comp_out == 4'b0010) || (comp_out == 4'b0111)
    );

    // OUT maps greater comparator result to 01.
    check_out_from_comp_gt: assert property (
        @($global_clock) disable iff (1'b0)
        (comp_out == 4'b0001) |-> (OUT == 2'b01)
    );

    // OUT maps less comparator result to 10.
    check_out_from_comp_lt: assert property (
        @($global_clock) disable iff (1'b0)
        (comp_out == 4'b0010) |-> (OUT == 2'b10)
    );

    // OUT maps equal comparator result to 11.
    check_out_from_comp_eq: assert property (
        @($global_clock) disable iff (1'b0)
        (comp_out == 4'b0111) |-> (OUT == 2'b11)
    );

    // OUT is restricted to the implemented encodings.
    check_out_valid_codes: assert property (
        @($global_clock) disable iff (1'b0)
        (OUT == 2'b01) || (OUT == 2'b10) || (OUT == 2'b11)
    );

    // OUT=01 implies the addsub low nibble is greater than in0 low nibble.
    check_out_gt_meaning: assert property (
        @($global_clock) disable iff (1'b0)
        (OUT == 2'b01) |-> (addsub_out[3:0] > in0[3:0])
    );

    // OUT=10 implies the addsub low nibble is less than in0 low nibble.
    check_out_lt_meaning: assert property (
        @($global_clock) disable iff (1'b0)
        (OUT == 2'b10) |-> (addsub_out[3:0] < in0[3:0])
    );

    // OUT=11 implies the compared low nibbles are equal.
    check_out_eq_meaning: assert property (
        @($global_clock) disable iff (1'b0)
        (OUT == 2'b11) |-> (addsub_out[3:0] == in0[3:0])
    );

endmodule