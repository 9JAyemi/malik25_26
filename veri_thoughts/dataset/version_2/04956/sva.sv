module bit_manipulation_sva (
    input logic       clk,
    input logic [3:0] I,
    input logic [1:0] O
);

    // Output encoding is determined solely by I[3].
    check_output_matches_i3: assert property (
        @(posedge clk) disable iff (1'b0) O == {I[3], ~I[3]}
    );

    // O[0] is the inverse of I[3].
    check_o0_inverts_i3: assert property (
        @(posedge clk) disable iff (1'b0) O[0] == ~I[3]
    );

    // O[1] matches I[3].
    check_o1_matches_i3: assert property (
        @(posedge clk) disable iff (1'b0) O[1] == I[3]
    );

    // Exactly one output bit is high at all times.
    check_output_onehot: assert property (
        @(posedge clk) disable iff (1'b0) O[0] ^ O[1]
    );

    // I[3] low produces output 2'b01.
    check_i3_low_encoding: assert property (
        @(posedge clk) disable iff (1'b0) !I[3] |-> O == 2'b01
    );

    // I[3] high produces output 2'b10.
    check_i3_high_encoding: assert property (
        @(posedge clk) disable iff (1'b0) I[3] |-> O == 2'b10
    );

    // If I[3] is unchanged across samples, O stays unchanged.
    check_output_stable_when_i3_stable: assert property (
        @(posedge clk) disable iff (1'b0) (!$initstate && $stable(I[3])) |-> $stable(O)
    );

    // A rising I[3] drives the output to 2'b10.
    check_i3_rise_encoding: assert property (
        @(posedge clk) disable iff (1'b0) $rose(I[3]) |-> O == 2'b10
    );

    // A falling I[3] drives the output to 2'b01.
    check_i3_fall_encoding: assert property (
        @(posedge clk) disable iff (1'b0) $fell(I[3]) |-> O == 2'b01
    );

endmodule