module my_2to1_mux_sva (
    input logic CLK,
    input logic [16:0] MO,
    input logic [16:0] A,
    input logic [16:0] B,
    input logic S
);

// MO equals B when S==1.
    check_select_b_when_s1: assert property (
        @(posedge CLK) (S == 1'b1) |-> (MO == B)
    );

// MO equals A when S==0.
    check_select_a_when_s0: assert property (
        @(posedge CLK) (S == 1'b0) |-> (MO == A)
    );

// MO equals A when S is unknown (X/Z).
    check_select_a_when_s_unknown: assert property (
        @(posedge CLK) (S != 1'b1) |-> (MO == A)
    );

// MO equals B when S is unknown (X/Z).
    check_select_b_when_s_unknown: assert property (
        @(posedge CLK) (S != 1'b0) |-> (MO == B)
    );

// MO equals A when both inputs are equal.
    check_equal_inputs_select_a: assert property (
        @(posedge CLK) (A == B) |-> (MO == A)
    );

endmodule
