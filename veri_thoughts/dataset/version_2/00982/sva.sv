module components_dff_en_rst_sva #(
    parameter int WIDTH = 1,
    parameter [WIDTH-1:0] RESET_VAL = '0
) (
    input logic                  clk,
    input logic                  rst,   // active-HIGH synchronous reset
    input logic                  en,
    input logic [WIDTH-1:0]      d,
    input logic [WIDTH-1:0]      q
);
    ///// Reset behavior /////
    // On a cycle with rst HIGH, q is driven to RESET_VAL on the next cycle.
    check_sync_reset_load_next: assert property (
        @(posedge clk) rst |=> (q == RESET_VAL)
    );
    // While rst remains HIGH across cycles, q holds RESET_VAL.
    check_reset_holds_value: assert property (
        @(posedge clk) (rst && $past(rst)) |-> (q == RESET_VAL)
    );

    ///// Enable behavior when not in reset /////
    // With en HIGH (and not in reset), q updates to d on the next cycle.
    check_update_on_en_when_not_reset: assert property (
        @(posedge clk) disable iff (rst) (en == 1'b1) |=> (q == $past(d))
    );
    // With en LOW (and not in reset), q holds its previous value.
    check_hold_when_en_low_not_reset: assert property (
        @(posedge clk) disable iff (rst) (en == 1'b0) |=> (q == $past(q))
    );
endmodule


module components_dff_en_sva #(
    parameter int WIDTH = 1
) (
    input logic                  clk,
    input logic                  en,
    input logic [WIDTH-1:0]      d,
    input logic [WIDTH-1:0]      q
);
    ///// Enable behavior /////
    // With en HIGH, q updates to d on the next cycle.
    check_update_on_en: assert property (
        @(posedge clk) (en == 1'b1) |=> (q == $past(d))
    );
    // With en LOW, q holds its previous value.
    check_hold_when_en_low: assert property (
        @(posedge clk) (en == 1'b0) |=> (q == $past(q))
    );
endmodule


module components_dff_sva #(
    parameter int WIDTH = 1
) (
    input logic                  clk,
    input logic [WIDTH-1:0]      d,
    input logic [WIDTH-1:0]      q
);
    ///// DFF behavior /////
    // q updates to the previous cycle's d every clock.
    check_dff_transparent_each_cycle: assert property (
        @(posedge clk) 1'b1 |=> (q == $past(d))
    );
endmodule