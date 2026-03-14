module decoder_2to4_sva (
    input logic clk,
    input logic [1:0] in,
    input logic [3:0] out
);
    // Output equals one-hot decode of prior input.
    check_registered_decode: assert property (
        @(posedge clk) disable iff ($initstate) out == (4'b0001 << $past(in))
    );

    // Output is always one-hot after initialization.
    check_out_onehot: assert property (
        @(posedge clk) disable iff ($initstate) $onehot(out)
    );

    // Output is always one of the four valid one-hot values.
    check_out_valid_set: assert property (
        @(posedge clk) disable iff ($initstate) (out inside {4'b0001,4'b0010,4'b0100,4'b1000})
    );

    // If input is unchanged for two consecutive cycles, output holds its value.
    check_hold_when_input_stable: assert property (
        @(posedge clk) disable iff ($initstate) ($past(in) == $past(in,2)) |-> (out == $past(out))
    );

    // If input changes between the last two cycles, output changes accordingly.
    check_change_when_input_changes: assert property (
        @(posedge clk) disable iff ($initstate) ($past(in) != $past(in,2)) |-> (out != $past(out))
    );
endmodule