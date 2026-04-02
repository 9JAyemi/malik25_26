module reset_sync_sva (
    input logic clk,
    input logic reset_n,
    output logic reset_n_sync
);

    // Synchronization of reset signal across multiple stages
    sync_reset: assert property (
        @(posedge clk) disable iff (!reset_n) $stable(reset_n_sync)
    ) else $error("Reset signal not synchronized correctly across stages");

    // Reset signal should be low after synchronization
    reset_low: assert property (
        @(posedge clk) disable iff (!reset_n) reset_n_sync |-> reset_n == 1'b0
    ) else $error("Reset signal not low after synchronization");

endmodule