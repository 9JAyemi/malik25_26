module priority_encoder_sva (
    input logic [3:0] I,
    input logic [1:0] O
);

    // 0001 encodes to 00.
    check_encode_0001: assert property (
        @($global_clock) (I == 4'b0001) |-> (O == 2'b00)
    );

    // 0010 encodes to 01.
    check_encode_0010: assert property (
        @($global_clock) (I == 4'b0010) |-> (O == 2'b01)
    );

    // 0100 encodes to 10.
    check_encode_0100: assert property (
        @($global_clock) (I == 4'b0100) |-> (O == 2'b10)
    );

    // 1000 encodes to 11.
    check_encode_1000: assert property (
        @($global_clock) (I == 4'b1000) |-> (O == 2'b11)
    );

    // All other known inputs return the default 00.
    check_default_for_other_known_inputs: assert property (
        @($global_clock)
        (!$isunknown(I) &&
         (I != 4'b0001) &&
         (I != 4'b0010) &&
         (I != 4'b0100) &&
         (I != 4'b1000)) |-> (O == 2'b00)
    );

endmodule