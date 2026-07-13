module bin2gray_sva (
    input logic [3:0] bin,
    input logic [3:0] gray,
    input logic reset,
    input logic clk
);
    // reset is active-high synchronous; clock is posedge clk; logic is sequential with 1-cycle latency.

    // On a reset cycle, gray is cleared on the next cycle.
    reset_clears_gray_next: assert property (
        @(posedge clk) reset |=> (gray == 4'b0000)
    );

    // When not in reset, next-cycle gray equals Gray-code of previous-cycle bin.
    gray_updates_to_prev_bin: assert property (
        @(posedge clk) disable iff (reset)
            (!reset) |=> (gray == ($past(bin) ^ ($past(bin) >> 1)))
    );

    // MSB rule: next-cycle gray[3] equals previous-cycle bin[3] when not in reset.
    gray_bit3_matches_prev_b3: assert property (
        @(posedge clk) disable iff (reset)
            (!reset) |=> (gray[3] == $past(bin[3]))
    );

    // Bit[2] rule: next-cycle gray[2] equals previous-cycle bin[3] ^ bin[2] when not in reset.
    gray_bit2_matches_prev_b3_xor_b2: assert property (
        @(posedge clk) disable iff (reset)
            (!reset) |=> (gray[2] == ($past(bin[3]) ^ $past(bin[2])))
    );

    // Bit[1] rule: next-cycle gray[1] equals previous-cycle bin[2] ^ bin[1] when not in reset.
    gray_bit1_matches_prev_b2_xor_b1: assert property (
        @(posedge clk) disable iff (reset)
            (!reset) |=> (gray[1] == ($past(bin[2]) ^ $past(bin[1])))
    );

    // Bit[0] rule: next-cycle gray[0] equals previous-cycle bin[1] ^ bin[0] when not in reset.
    gray_bit0_matches_prev_b1_xor_b0: assert property (
        @(posedge clk) disable iff (reset)
            (!reset) |=> (gray[0] == ($past(bin[1]) ^ $past(bin[0])))
    );

    // If bin is stable across two consecutive non-reset cycles, gray remains stable.
    gray_stable_when_bin_stable: assert property (
        @(posedge clk) disable iff (reset)
            ($past(!reset) && $past(!reset,2) && ($past(bin) == $past(bin,2))) |-> (gray == $past(gray))
    );
endmodule