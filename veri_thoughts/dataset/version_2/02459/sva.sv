module shift_register_sva (
    input logic clk,
    input logic in,
    input logic [2:0] out,
    input logic [2:0] reg_out
);
    ///// Combinational mapping /////
    // out mirrors reg_out masked by 3'b111.
    out_follows_reg_out_masked: assert property (
        @(posedge clk) out == (reg_out & 3'b111)
    );

    ///// Sequential shift behavior /////
    // reg_out updates to {previous reg_out[1:0], previous in}.
    reg_out_shift_concat: assert property (
        @(posedge clk) $past(1'b1) |-> reg_out == {$past(reg_out[1:0]), $past(in)}
    );
    // Bit 0 of reg_out captures in on the next clock.
    shift_bit0_captures_in: assert property (
        @(posedge clk) $past(1'b1) |-> reg_out[0] == $past(in)
    );
    // Bit 1 of reg_out shifts from previous bit 0.
    shift_bit1_from_bit0: assert property (
        @(posedge clk) $past(1'b1) |-> reg_out[1] == $past(reg_out[0])
    );
    // Bit 2 of reg_out shifts from previous bit 1.
    shift_bit2_from_bit1: assert property (
        @(posedge clk) $past(1'b1) |-> reg_out[2] == $past(reg_out[1])
    );

    ///// Stability relation /////
    // If reg_out is unchanged cycle-to-cycle, out is unchanged.
    out_stable_when_reg_out_stable: assert property (
        @(posedge clk) $past(1'b1) && (reg_out == $past(reg_out)) |-> (out == $past(out))
    );

    ///// 3-cycle input history determines state /////
    // After 3 cycles, reg_out equals the last 3 inputs (oldest->newest).
    reg_out_equals_3past_inputs: assert property (
        @(posedge clk) $past(1'b1,3) |-> reg_out == { $past(in,3), $past(in,2), $past(in,1) }
    );
    // After 3 cycles, out equals masked last 3 inputs.
    out_equals_masked_3past_inputs: assert property (
        @(posedge clk) $past(1'b1,3) |-> out == ({ $past(in,3), $past(in,2), $past(in,1) } & 3'b111)
    );

    ///// Special cases of the 3-cycle history /////
    // Three consecutive zeros on in drive reg_out to 3'b000.
    zeros_flush_reg_out_in3: assert property (
        @(posedge clk) $past(1'b1,3) && ($past(in,3)==1'b0) && ($past(in,2)==1'b0) && ($past(in,1)==1'b0) |-> (reg_out == 3'b000)
    );
    // Three consecutive ones on in drive reg_out to 3'b111.
    ones_fill_reg_out_in3: assert property (
        @(posedge clk) $past(1'b1,3) && ($past(in,3)==1'b1) && ($past(in,2)==1'b1) && ($past(in,1)==1'b1) |-> (reg_out == 3'b111)
    );

endmodule