module xor2_sva (
    input logic a,
    input logic b,
    input logic z
);
    // Analysis: no clock or reset in RTL; purely combinational with #DELAY on assignment.
    // Functional behavior: z updates to a ^ b after DELAY time units when a or b changes.
    // With no clock/reset exposed by the RTL and timing-based behavior, no sound clocked SVA can be written without inventing signals.
endmodule