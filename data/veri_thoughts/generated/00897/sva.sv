module xor_32_sva (
    input logic CLK,
    input logic [31:0] X,
    input logic [31:0] Y,
    input logic [31:0] Dout
);
    // Clock: CLK (posedge). No reset in RTL; mask first cycle with $initstate.
    // Sequential: Dout is a 1-cycle-registered XOR of X and Y.

    // Dout equals previous cycle's bitwise XOR of X and Y.
    check_dout_pipeline_xor: assert property (
        @(posedge CLK) disable iff ($initstate) (Dout == $past(X ^ Y))
    );

    // If X equals Y in this cycle, Dout is zero next cycle.
    check_zero_when_inputs_equal: assert property (
        @(posedge CLK) disable iff ($initstate) (X == Y) |=> (Dout == 32'b0)
    );

    // If X is bitwise complement of Y in this cycle, Dout is all ones next cycle.
    check_allones_when_inputs_complementary: assert property (
        @(posedge CLK) disable iff ($initstate) (X == ~Y) |=> (Dout == 32'hFFFF_FFFF)
    );

    // If Y is zero in this cycle, Dout equals prior X next cycle.
    check_prevY_zero_passes_prevX: assert property (
        @(posedge CLK) disable iff ($initstate) (Y == 32'b0) |=> (Dout == $past(X))
    );

    // If X is zero in this cycle, Dout equals prior Y next cycle.
    check_prevX_zero_passes_prevY: assert property (
        @(posedge CLK) disable iff ($initstate) (X == 32'b0) |=> (Dout == $past(Y))
    );

    // If Y is all ones in this cycle, Dout equals bitwise NOT of prior X next cycle.
    check_prevY_ones_inverts_prevX: assert property (
        @(posedge CLK) disable iff ($initstate) (Y == 32'hFFFF_FFFF) |=> (Dout == ~ $past(X))
    );

    // If X is all ones in this cycle, Dout equals bitwise NOT of prior Y next cycle.
    check_prevX_ones_inverts_prevY: assert property (
        @(posedge CLK) disable iff ($initstate) (X == 32'hFFFF_FFFF) |=> (Dout == ~ $past(Y))
    );

endmodule