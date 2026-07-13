module binary_counter_sva (
    input logic clk,
    input logic rst,
    input logic en,
    input logic load,
    input logic [3:0] load_value,
    input logic [3:0] out
);

    ///// Reset behavior /////
    // When rst is HIGH at a clock edge, out must be 0.
    reset_forces_zero_now: assert property (
        @(posedge clk) rst |-> (out == 4'b0000)
    );

    // On a rising edge of rst between clocks, out must be 0 at the next sample.
    reset_rise_clears_out: assert property (
        @(posedge clk) $rose(rst) |-> (out == 4'b0000)
    );

    ///// Load and count behavior /////
    // With load asserted, next out equals previous load_value.
    next_on_load: assert property (
        @(posedge clk) disable iff (rst) load |=> (out == $past(load_value))
    );

    // With en asserted and load deasserted, next out increments by 1 (mod 16).
    next_on_en_no_load: assert property (
        @(posedge clk) disable iff (rst) (en && !load) |=> (out == $past(out) + 4'd1)
    );

    // With neither en nor load, out holds its previous value.
    hold_when_idle: assert property (
        @(posedge clk) disable iff (rst) (!en && !load) |=> (out == $past(out))
    );

    // load has priority over en when both are HIGH.
    load_has_priority_over_en: assert property (
        @(posedge clk) disable iff (rst) (load && en) |=> (out == $past(load_value))
    );

    // Increment from 4'hF wraps to 4'h0 when en is asserted and no load.
    wrap_from_max: assert property (
        @(posedge clk) disable iff (rst) (en && !load && (out == 4'hF)) |=> (out == 4'h0)
    );

endmodule