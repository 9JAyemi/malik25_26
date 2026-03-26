module Span12Mux_s0_h_sva (
    input logic [11:0] I,
    input logic [2:0]  s,
    input logic [11:0] O
);

    // Select values 000 through 110 pass the input bus to the output.
    check_non_111_selects_pass_input: assert property (
        @($global_clock)
        ((s === 3'b000) || (s === 3'b001) || (s === 3'b010) || (s === 3'b011) ||
         (s === 3'b100) || (s === 3'b101) || (s === 3'b110))
        |-> (O === I)
    );

    // Select value 111 drives the output bus to zero.
    check_sel_111_drives_zero: assert property (
        @($global_clock)
        (s === 3'b111) |-> (O === 12'b0)
    );

endmodule