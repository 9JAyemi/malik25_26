module register_4bit_sva (
    input logic CLK,
    input logic [3:0] D,
    input logic LD,
    input logic RST,
    input logic [3:0] Q
);

    // Reset forces the register output to zero.
    check_reset_clears_q: assert property (
        @(posedge CLK) RST |-> (Q == 4'b0000)
    );

    // A load captures D into Q on the next clock.
    check_load_captures_d: assert property (
        @(posedge CLK) disable iff (RST) LD |=> (Q == $past(D))
    );

    // With load deasserted, Q holds its previous value.
    check_hold_when_ld_low: assert property (
        @(posedge CLK) disable iff (RST) !LD |=> $stable(Q)
    );

    // Loading a new value causes Q to change to that value.
    check_load_new_value_changes_q: assert property (
        @(posedge CLK) disable iff (RST) (LD && (D != Q)) |=> ((Q == $past(D)) && !$stable(Q))
    );

    // Loading the current value leaves Q unchanged.
    check_load_same_value_keeps_q_stable: assert property (
        @(posedge CLK) disable iff (RST) (LD && (D == Q)) |=> $stable(Q)
    );

    // After reset release, Q stays zero if no load is requested.
    check_reset_release_keeps_zero_without_load: assert property (
        @(posedge CLK) RST ##1 (!RST && !LD) |-> (Q == 4'b0000)
    );

endmodule