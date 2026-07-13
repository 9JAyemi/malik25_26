module First_Phase_M_W32_sva (
    input logic clk,
    input logic rst,
    input logic load,
    input logic [31:0] Data_MX,
    input logic [31:0] Data_MY,
    input logic [31:0] Op_MX,
    input logic [31:0] Op_MY
);
    ///// Reset behavior (active-high synchronous) /////
    // If rst is HIGH at a clock edge, outputs are zero on the next cycle.
    reset_clears_outputs_next: assert property (
        @(posedge clk) rst |=> (Op_MX == 32'h0) && (Op_MY == 32'h0)
    );
    // While rst is held HIGH for 2+ cycles, outputs remain zero.
    reset_holds_zero: assert property (
        @(posedge clk) (rst && $past(rst)) |-> (Op_MX == 32'h0) && (Op_MY == 32'h0)
    );

    ///// Load/capture behavior /////
    // With load HIGH and not in reset, Op_MX captures Data_MX on the next cycle.
    capture_mx_on_load: assert property (
        @(posedge clk) disable iff (rst) load |=> (Op_MX == $past(Data_MX))
    );
    // With load HIGH and not in reset, Op_MY captures Data_MY on the next cycle.
    capture_my_on_load: assert property (
        @(posedge clk) disable iff (rst) load |=> (Op_MY == $past(Data_MY))
    );

    ///// Hold behavior when not loading /////
    // With load LOW and not in reset, Op_MX holds its previous value.
    hold_mx_without_load: assert property (
        @(posedge clk) disable iff (rst) !load |=> (Op_MX == $past(Op_MX))
    );
    // With load LOW and not in reset, Op_MY holds its previous value.
    hold_my_without_load: assert property (
        @(posedge clk) disable iff (rst) !load |=> (Op_MY == $past(Op_MY))
    );

    ///// Change qualification /////
    // Any change on Op_MX must be caused by prior load or prior reset.
    mx_change_requires_prior_load_or_reset: assert property (
        @(posedge clk) disable iff (rst) (Op_MX != $past(Op_MX)) |-> ($past(load) || $past(rst))
    );
    // Any change on Op_MY must be caused by prior load or prior reset.
    my_change_requires_prior_load_or_reset: assert property (
        @(posedge clk) disable iff (rst) (Op_MY != $past(Op_MY)) |-> ($past(load) || $past(rst))
    );

    ///// Behavior around reset release /////
    // On the cycle after reset (previous cycle rst=1) with no load, outputs remain zero.
    release_reset_no_load_keeps_zero: assert property (
        @(posedge clk) disable iff (rst) ($past(rst) && !load) |-> (Op_MX == 32'h0) && (Op_MY == 32'h0)
    );
    // On the cycle after reset (previous cycle rst=1) with load HIGH, next outputs capture current data.
    release_reset_with_load_captures_data: assert property (
        @(posedge clk) disable iff (rst) ($past(rst) && load) |=> (Op_MX == $past(Data_MX)) && (Op_MY == $past(Data_MY))
    );
endmodule