module binary_to_gray_sva (
    input logic [3:0] in,
    input logic       load,
    input logic [3:0] out,
    input logic       valid
);

    // Load high drives the registered outputs and valid on the next cycle.
    check_load_updates_outputs_and_valid: assert property (
        @(posedge load) 1 |=> (out == $past((in >> 1) ^ in)) && (valid == 1'b1)
    );

    // Load low clears valid on the next cycle.
    check_load_low_clears_valid: assert property (
        @(posedge load) !load |=> (valid == 1'b0)
    );

    // Load low leaves out unchanged on the next cycle.
    check_load_low_holds_out: assert property (
        @(posedge load) !load |=> (out == $past(out))
    );

    // valid is high exactly one cycle after a load high.
    check_valid_one_cycle_after_load: assert property (
        @(posedge load) 1 |=> ##1 valid
    );

    // valid is low exactly one cycle after a load low.
    check_valid_low_one_cycle_after_load_low: assert property (
        @(posedge load) !load |=> ##1 !valid
    );

    // valid is high exactly one cycle after a load high and low.
    check_valid_one_cycle_after_load_or_load_low: assert property (
        @(posedge load) 1 |=> ##1 valid
    );

    // valid is low exactly one cycle after a load low and high.
    check_valid_low_one_cycle_after_load_low_or_load: assert property (
        @(posedge load) !load |=> ##1 !valid
    );

endmodule