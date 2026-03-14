module sky130_fd_sc_ms__xor3_sva (
    input logic X,
    input logic A,
    input logic B,
    input logic C
);
    // X equals A^B^C when A rises.
    check_parity_posA: assert property (
        @(posedge A) X == (A ^ B ^ C)
    );
    // X equals A^B^C when A falls.
    check_parity_negA: assert property (
        @(negedge A) X == (A ^ B ^ C)
    );
    // X equals A^B^C when B rises.
    check_parity_posB: assert property (
        @(posedge B) X == (A ^ B ^ C)
    );
    // X equals A^B^C when B falls.
    check_parity_negB: assert property (
        @(negedge B) X == (A ^ B ^ C)
    );
    // X equals A^B^C when C rises.
    check_parity_posC: assert property (
        @(posedge C) X == (A ^ B ^ C)
    );
    // X equals A^B^C when C falls.
    check_parity_negC: assert property (
        @(negedge C) X == (A ^ B ^ C)
    );
    // X equals A^B^C when X rises.
    check_parity_posX: assert property (
        @(posedge X) X == (A ^ B ^ C)
    );
    // X equals A^B^C when X falls.
    check_parity_negX: assert property (
        @(negedge X) X == (A ^ B ^ C)
    );
    // X does not rise unless at least one input changed.
    check_x_rise_caused_by_inputs: assert property (
        @(posedge X) ($changed(A) || $changed(B) || $changed(C))
    );
    // X does not fall unless at least one input changed.
    check_x_fall_caused_by_inputs: assert property (
        @(negedge X) ($changed(A) || $changed(B) || $changed(C))
    );
endmodule