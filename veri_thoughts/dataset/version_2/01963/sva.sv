module top_module_sva (
    input logic clk,
    input logic [7:0] in,
    input logic [7:0] anyedge
);

    // Internal history-valid flags (no reset in RTL)
    logic init1, init2;
    always_ff @(posedge clk) begin
        init1 <= 1'b1;
        init2 <= init1;
    end

    ///// Functional equivalence to 3-sample pulse detector /////
    // After 2 cycles of history, anyedge == (~in & $past(in) & ~$past(in,2)).
    eq_anyedge_function: assert property (
        @(posedge clk) init2 |-> (anyedge == ((~in) & $past(in) & (~$past(in,2))))
    );

    ///// Basic masking rules /////
    // anyedge never asserts on bits where current in is 1.
    anyedge_masked_by_in_zero: assert property (
        @(posedge clk) (anyedge & in) == 8'h00
    );

    ///// Stability implications /////
    // If in didn't change from previous cycle, no pulse can occur.
    no_pulse_when_no_change_prev: assert property (
        @(posedge clk) init1 && ($past(in) == in) |-> (anyedge == 8'h00)
    );
    // If in[t-2] == in[t-1], no pulse can occur at t.
    no_pulse_when_no_change_prev2: assert property (
        @(posedge clk) init2 && ($past(in,2) == $past(in)) |-> (anyedge == 8'h00)
    );

    ///// Necessary conditions for anyedge /////
    // When anyedge is high, the previous in must be high (per bit).
    anyedge_requires_prev_in_high: assert property (
        @(posedge clk) init1 |-> ((anyedge & ~($past(in))) == 8'h00)
    );
    // When anyedge is high, in from two cycles ago must be low (per bit).
    anyedge_requires_prev2_in_low: assert property (
        @(posedge clk) init2 |-> ((anyedge & $past(in,2)) == 8'h00)
    );

    ///// Pulse shape /////
    // No bit of anyedge can be high in two consecutive cycles.
    no_back_to_back_anyedge: assert property (
        @(posedge clk) init1 |-> ((anyedge & $past(anyedge)) == 8'h00)
    );

    ///// Per-bit detection of single-cycle high on input /////
    genvar i;
    for (i = 0; i < 8; i++) begin : gen_bit
        // A 0->1->0 pattern on in[i] produces a pulse on anyedge[i] at the last cycle.
        detect_single_cycle_pulse: assert property (
            @(posedge clk) (!in[i]) ##1 (in[i]) ##1 (!in[i]) |-> anyedge[i]
        );
    end

endmodule