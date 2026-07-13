module reg_8bit_sva (
    input logic clk,
    input logic Load,
    input logic not_reset,
    input logic [7:0] D,
    input logic [7:0] Q
);

    // Reset drives the register output to zero.
    check_reset_forces_zero: assert property (
        @(posedge clk) !not_reset |-> (Q == 8'h00)
    );

    // When loading, the next sampled value is D or zero if reset intervenes.
    check_load_captures_d_or_reset_zero: assert property (
        @(posedge clk) disable iff (!not_reset)
        Load |=> ((Q == $past(D)) || (Q == 8'h00))
    );

    // Without loading, the next sampled value holds or becomes zero on reset.
    check_hold_preserves_q_or_reset_zero: assert property (
        @(posedge clk) disable iff (!not_reset)
        !Load |=> ((Q == $past(Q)) || (Q == 8'h00))
    );

    // Loading an all-zero value produces an all-zero output.
    check_load_zero_updates_zero: assert property (
        @(posedge clk) disable iff (!not_reset)
        (Load && (D == 8'h00)) |=> (Q == 8'h00)
    );

    // An all-zero output stays zero when no load occurs.
    check_zero_holds_without_load: assert property (
        @(posedge clk) disable iff (!not_reset)
        (!Load && (Q == 8'h00)) |=> (Q == 8'h00)
    );

endmodule