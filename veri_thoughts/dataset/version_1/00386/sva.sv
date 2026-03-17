module adder_4bit_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       CIN,
    input logic       CLK,
    input logic       RST,
    input logic [3:0] SUM,
    input logic       COUT
);

    // During active-low reset, the registered outputs are cleared.
    check_reset_clears_outputs: assert property (
        @(posedge CLK) (!RST) |-> (SUM == 4'b0000 && COUT == 1'b0)
    );

    // On the first clock after reset release, outputs are still the reset values.
    check_first_cycle_after_reset_release_is_zero: assert property (
        @(posedge CLK) disable iff (!RST) $rose(RST) |-> (SUM == 4'b0000 && COUT == 1'b0)
    );

    // SUM reflects the prior cycle's truncated A+B+CIN result.
    check_sum_matches_previous_inputs: assert property (
        @(posedge CLK) disable iff (!RST)
        $past(RST) |-> (SUM == $past(A + B + CIN))
    );

    // COUT reflects the prior cycle's registered MSB majority function.
    check_cout_matches_previous_inputs: assert property (
        @(posedge CLK) disable iff (!RST)
        $past(RST) |-> (COUT == $past((A[3] & B[3]) | (A[3] & CIN) | (B[3] & CIN)))
    );

    // A full-scale add wraps SUM and drives COUT high on the following cycle.
    check_full_scale_add_behavior: assert property (
        @(posedge CLK) disable iff (!RST)
        $past(RST) && ($past(A) == 4'hF) && ($past(B) == 4'hF) && $past(CIN)
        |-> (SUM == 4'hF && COUT == 1'b1)
    );

endmodule