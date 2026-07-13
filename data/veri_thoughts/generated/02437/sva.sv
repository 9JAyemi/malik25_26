module CapBoardDriver_sva (
    input logic clk500kHz,
    input logic [3:0] state,
    input logic [7:0] fets
);
    // fets[3:0] must equal {4{clk500kHz}} & state
    check_fets_lo_assign: assert property (
        @(posedge clk500kHz) fets[3:0] == ({4{clk500kHz}} & state)
    );

    // fets[7:4] must equal (~fets[3:0]) & state
    check_fets_hi_assign: assert property (
        @(posedge clk500kHz) fets[7:4] == ((~fets[3:0]) & state)
    );

    // When state[0]==0, fets[0]==0
    check_lo_zero_when_state0_b0: assert property (
        @(posedge clk500kHz) (state[0] == 1'b0) |-> (fets[0] == 1'b0)
    );

    // When state[1]==0, fets[1]==0
    check_lo_zero_when_state0_b1: assert property (
        @(posedge clk500kHz) (state[1] == 1'b0) |-> (fets[1] == 1'b0)
    );

    // When state[2]==0, fets[2]==0
    check_lo_zero_when_state0_b2: assert property (
        @(posedge clk500kHz) (state[2] == 1'b0) |-> (fets[2] == 1'b0)
    );

    // When state[3]==0, fets[3]==0
    check_lo_zero_when_state0_b3: assert property (
        @(posedge clk500kHz) (state[3] == 1'b0) |-> (fets[3] == 1'b0)
    );

    // When state[0]==0, fets[4]==0
    check_hi_zero_when_state0_b0: assert property (
        @(posedge clk500kHz) (state[0] == 1'b0) |-> (fets[4] == 1'b0)
    );

    // When state[1]==0, fets[5]==0
    check_hi_zero_when_state0_b1: assert property (
        @(posedge clk500kHz) (state[1] == 1'b0) |-> (fets[5] == 1'b0)
    );

    // When state[2]==0, fets[6]==0
    check_hi_zero_when_state0_b2: assert property (
        @(posedge clk500kHz) (state[2] == 1'b0) |-> (fets[6] == 1'b0)
    );

    // When state[3]==0, fets[7]==0
    check_hi_zero_when_state0_b3: assert property (
        @(posedge clk500kHz) (state[3] == 1'b0) |-> (fets[7] == 1'b0)
    );
endmodule