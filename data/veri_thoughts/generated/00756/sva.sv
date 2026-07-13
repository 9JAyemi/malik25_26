module shift_register_sva (
    input logic [3:0] in,
    input logic       shift_dir,
    input logic       clk,
    input logic [3:0] out
);
    ///// Shift behavior /////
    // out equals in delayed by 3 clock cycles.
    check_out_is_in_delayed_3: assert property (
        @(posedge clk) 1'b1 |-> ##3 (out == $past(in,3))
    );

    // A rising edge on in[0] appears on out[0] after 3 cycles.
    propagate_rise_bit0_after3: assert property (
        @(posedge clk) $rose(in[0]) |-> ##3 $rose(out[0])
    );
    // A rising edge on in[1] appears on out[1] after 3 cycles.
    propagate_rise_bit1_after3: assert property (
        @(posedge clk) $rose(in[1]) |-> ##3 $rose(out[1])
    );
    // A rising edge on in[2] appears on out[2] after 3 cycles.
    propagate_rise_bit2_after3: assert property (
        @(posedge clk) $rose(in[2]) |-> ##3 $rose(out[2])
    );
    // A rising edge on in[3] appears on out[3] after 3 cycles.
    propagate_rise_bit3_after3: assert property (
        @(posedge clk) $rose(in[3]) |-> ##3 $rose(out[3])
    );

    // A falling edge on in[0] appears on out[0] after 3 cycles.
    propagate_fall_bit0_after3: assert property (
        @(posedge clk) $fell(in[0]) |-> ##3 $fell(out[0])
    );
    // A falling edge on in[1] appears on out[1] after 3 cycles.
    propagate_fall_bit1_after3: assert property (
        @(posedge clk) $fell(in[1]) |-> ##3 $fell(out[1])
    );
    // A falling edge on in[2] appears on out[2] after 3 cycles.
    propagate_fall_bit2_after3: assert property (
        @(posedge clk) $fell(in[2]) |-> ##3 $fell(out[2])
    );
    // A falling edge on in[3] appears on out[3] after 3 cycles.
    propagate_fall_bit3_after3: assert property (
        @(posedge clk) $fell(in[3]) |-> ##3 $fell(out[3])
    );
endmodule