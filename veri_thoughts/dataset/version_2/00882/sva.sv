module Span12Mux_s5_h_sva (
    input logic CLK,
    input logic [3:0] I,
    input logic [11:0] A,
    input logic [11:0] B,
    input logic [11:0] C,
    input logic [11:0] D,
    input logic [11:0] E,
    input logic [11:0] O
);
    // O selects A when I == 4'b0000.
    select_A_when_I_0000: assert property (
        @(posedge CLK) (I == 4'b0000) |-> (O == A)
    );

    // O selects B when I == 4'b0001.
    select_B_when_I_0001: assert property (
        @(posedge CLK) (I == 4'b0001) |-> (O == B)
    );

    // O selects C when I == 4'b0010.
    select_C_when_I_0010: assert property (
        @(posedge CLK) (I == 4'b0010) |-> (O == C)
    );

    // O selects D when I == 4'b0011.
    select_D_when_I_0011: assert property (
        @(posedge CLK) (I == 4'b0011) |-> (O == D)
    );

    // O selects E when I == 4'b0100.
    select_E_when_I_0100: assert property (
        @(posedge CLK) (I == 4'b0100) |-> (O == E)
    );

    // O drives zero for all other I values (4'b0101 through 4'b1111).
    default_zero_for_other_I: assert property (
        @(posedge CLK) (I inside {[4'h5:4'hF]}) |-> (O == 12'b0)
    );

    // O equals the full case expression result for all I values.
    full_mux_behavior: assert property (
        @(posedge CLK)
            O == ((I == 4'h0) ? A :
                  (I == 4'h1) ? B :
                  (I == 4'h2) ? C :
                  (I == 4'h3) ? D :
                  (I == 4'h4) ? E : 12'b0)
    );
endmodule