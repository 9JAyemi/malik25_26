module clock_divider_sva (
    input logic clk_in,
    input logic rst,               // active-low asynchronous reset
    input logic [7:0] divisor,
    input logic clk_out,
    input logic [7:0] counter      // internal DUT signal
);
    ///// Reset behavior /////
    // While reset is asserted low, clk_out and counter are driven to 0.
    reset_forces_zero: assert property (
        @(posedge clk_in) (!rst) |-> (clk_out == 1'b0) && (counter == 8'h00)
    );

    ///// Functional behavior /////
    // On match (counter == divisor), next cycle clk_out toggles and counter clears to 0.
    toggle_and_clear_on_match: assert property (
        @(posedge clk_in) disable iff (!rst) (counter == divisor) |=> (clk_out == ~$past(clk_out)) && (counter == 8'h00)
    );

    // On no match, next cycle counter increments by 1 (mod 256).
    inc_on_no_match: assert property (
        @(posedge clk_in) disable iff (!rst) (counter != divisor) |=> (counter == (($past(counter) + 8'd1) & 8'hFF))
    );

    // On no match, next cycle clk_out holds its value.
    hold_clk_out_on_no_match: assert property (
        @(posedge clk_in) disable iff (!rst) (counter != divisor) |=> (clk_out == $past(clk_out))
    );

    // Any change on clk_out implies the previous cycle had a match (counter == divisor).
    clk_out_change_implies_prev_match: assert property (
        @(posedge clk_in) disable iff (!rst) $changed(clk_out) |-> ($past(counter) == $past(divisor))
    );

    // Any change on clk_out is a true toggle (new value is inverse of old).
    clk_out_change_is_toggle: assert property (
        @(posedge clk_in) disable iff (!rst) $changed(clk_out) |-> (clk_out == ~$past(clk_out))
    );

    // Next counter value is either incremented by 1 (mod 256) or cleared to 0.
    counter_next_is_inc_or_zero: assert property (
        @(posedge clk_in) disable iff (!rst) 1'b1 |=> (counter == (($past(counter) + 8'd1) & 8'hFF)) || (counter == 8'h00)
    );
endmodule