module top_module_sva (
    input logic [2:0] vec,
    input logic       select,
    input logic [2:0] outv,
    input logic       o2,
    input logic       o1,
    input logic       o0
);

    // outv[0] is vec[0] gated by select.
    check_outv0_mux: assert property (
        @($global_clock) outv[0] == (select & vec[0])
    );

    // outv[1] is vec[1] gated by select.
    check_outv1_mux: assert property (
        @($global_clock) outv[1] == (select & vec[1])
    );

    // outv[2] is vec[2] gated by select.
    check_outv2_mux: assert property (
        @($global_clock) outv[2] == (select & vec[2])
    );

    // o2 directly reflects vec[2].
    check_o2_decoder: assert property (
        @($global_clock) o2 == vec[2]
    );

    // o1 is high when vec[1:0] are 00 or 11.
    check_o1_decoder: assert property (
        @($global_clock) o1 == ((vec[1:0] == 2'b00) || (vec[1:0] == 2'b11))
    );

    // o0 is high only when vec is 000.
    check_o0_decoder: assert property (
        @($global_clock) o0 == (vec == 3'b000)
    );

endmodule