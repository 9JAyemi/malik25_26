module simple_calculator_sva (
    input logic [7:0] A,
    input logic [7:0] B,
    input logic       OP,
    input logic       CLK,
    input logic       RST,
    input logic [7:0] C
);
    // On any reset cycle, C is 0 in the following cycle.
    reset_clears_next: assert property (
        @(posedge CLK) RST |=> (C == 8'h00)
    );

    // Immediately after a reset cycle, C must be 0.
    post_reset_zero: assert property (
        @(posedge CLK) $past(RST) |-> (C == 8'h00)
    );

    // With OP==1 and not in reset, next C equals previous (A - B) modulo 256.
    update_on_sub_op: assert property (
        @(posedge CLK) disable iff (RST) (OP == 1'b1) |=> (C == ($past(A) - $past(B))[7:0])
    );

    // With OP==0 and not in reset, next C equals previous (A + B) modulo 256.
    update_on_add_op: assert property (
        @(posedge CLK) disable iff (RST) (OP == 1'b0) |=> (C == ($past(A) + $past(B))[7:0])
    );

    // If previous cycle was not reset, C matches the selected operation from the previous cycle.
    combined_update_rule: assert property (
        @(posedge CLK) disable iff (RST) $past(!RST) |-> (C == ($past(OP) ? ($past(A) - $past(B))[7:0] : ($past(A) + $past(B))[7:0]))
    );

    // If not in reset across two cycles and inputs are unchanged, C must be unchanged.
    hold_when_inputs_stable: assert property (
        @(posedge CLK) disable iff (RST)
            (!$past(RST) && !RST && (A == $past(A)) && (B == $past(B)) && (OP == $past(OP)))
            |-> $stable(C)
    );

    // If C changes (and previous cycle not reset), at least one of A, B, or OP must have changed.
    output_change_implies_input_change: assert property (
        @(posedge CLK) disable iff (RST)
            (!$past(RST) && (C != $past(C))) |-> ((A != $past(A)) || (B != $past(B)) || (OP != $past(OP)))
    );
endmodule