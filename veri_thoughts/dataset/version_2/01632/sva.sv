module binary_to_gray_sva (
    input logic clk,
    input logic rst,
    input logic [3:0] B,
    input logic [3:0] G,
    input logic [3:0] B_reg,
    input logic [3:0] G_reg
);
    // During reset (active-low), internal registers are cleared to 0.
    reset_regs_zero: assert property (
        @(posedge clk) (!rst) |-> (B_reg == 4'b0000) && (G_reg == 4'b0000)
    );

    // During reset (active-low), output G is 0.
    reset_output_zero: assert property (
        @(posedge clk) (!rst) |-> (G == 4'b0000)
    );

    // G is a direct reflection of G_reg.
    check_output_driven_by_greg: assert property (
        @(posedge clk) disable iff (!rst) (G == G_reg)
    );

    // B is sampled into B_reg each cycle (1-cycle latency).
    check_breg_captures_b: assert property (
        @(posedge clk) disable iff (!rst) $past(rst) |-> (B_reg == $past(B))
    );

    // G_reg computes Gray code from previous B_reg.
    check_greg_from_prev_breg: assert property (
        @(posedge clk) disable iff (!rst) $past(rst) |-> (
            G_reg == { $past(B_reg[3]),
                       $past(B_reg[3]) ^ $past(B_reg[2]),
                       $past(B_reg[2]) ^ $past(B_reg[1]),
                       $past(B_reg[1]) ^ $past(B_reg[0]) }
        )
    );

    // G equals Gray code of previous B (end-to-end 1-cycle latency).
    check_g_from_prev_b: assert property (
        @(posedge clk) disable iff (!rst) $past(rst) |-> (
            G == { $past(B[3]),
                   $past(B[3]) ^ $past(B[2]),
                   $past(B[2]) ^ $past(B[1]),
                   $past(B[1]) ^ $past(B[0]) }
        )
    );

    // On reset deassertion edge, outputs reflect zeros from previously reset state.
    check_zero_on_reset_release: assert property (
        @(posedge clk) disable iff (!rst) $rose(rst) |-> (B_reg == 4'b0000) && (G_reg == 4'b0000) && (G == 4'b0000)
    );

    // If B is unchanged for two consecutive cycles, G is unchanged next cycle.
    check_g_stable_when_b_stable: assert property (
        @(posedge clk) disable iff (!rst) $past(rst,2) && ($past(B,1) == $past(B,2)) |-> (G == $past(G))
    );

    // MSB of G equals previous cycle's MSB of B.
    check_g_msb_from_prev_b_msb: assert property (
        @(posedge clk) disable iff (!rst) $past(rst) |-> (G[3] == $past(B[3]))
    );

    // MSB of G_reg equals previous cycle's MSB of B_reg.
    check_greg_msb_from_prev_breg_msb: assert property (
        @(posedge clk) disable iff (!rst) $past(rst) |-> (G_reg[3] == $past(B_reg[3]))
    );
endmodule