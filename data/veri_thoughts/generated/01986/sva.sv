module barrel_shifter_priority_encoder_or_sva (
    input logic clk,
    input logic load,
    input logic [1:0] ena,
    input logic [7:0] in,
    input logic [99:0] data,
    input logic [7:0] out,
    // Internal signals from DUT (bind via hierarchy)
    input logic [99:0] shifted_data,
    input logic [7:0] priority_encoded
);
    ///// Sequential barrel shifter behavior /////
    // On load, shifted_data captures data on next cycle.
    shift_on_load_updates_data: assert property (
        @(posedge clk) load |=> (shifted_data === $past(data))
    );
    // With both ena bits set and not loading, shifted_data equals data on next cycle.
    shift_both_ena_no_rotate: assert property (
        @(posedge clk) (!load && (ena[0] && ena[1])) |=> (shifted_data === $past(data))
    );
    // With ena[0] only and not loading, shifted_data rotates left by 1 from data on next cycle.
    shift_left_rotate: assert property (
        @(posedge clk) (!load && (ena[0] && !ena[1])) |=> (shifted_data === { $past(data[98:0]), $past(data[99]) })
    );
    // With ena[1] only and not loading, shifted_data rotates right by 1 from data on next cycle.
    shift_right_rotate: assert property (
        @(posedge clk) (!load && (!ena[0] && ena[1])) |=> (shifted_data === { $past(data[0]), $past(data[99:1]) })
    );

    ///// Priority encoder to output OR mapping /////
    // If shifted_data[99] is 1, out[7] is forced high and lower bits pass through.
    out_follows_priority_99: assert property (
        @(posedge clk) shifted_data[99] |-> (out[7] == 1'b1) && (out[6:0] === in[6:0])
    );
    // If highest set bit is 98, out[6] is forced high and others pass through.
    out_follows_priority_98: assert property (
        @(posedge clk) (!shifted_data[99] && shifted_data[98]) |-> (out[6] == 1'b1) && (out[7] == in[7]) && (out[5:0] === in[5:0])
    );
    // If highest set bit is 97, out[5] is forced high and others pass through.
    out_follows_priority_97: assert property (
        @(posedge clk) (!shifted_data[99] && !shifted_data[98] && shifted_data[97]) |-> (out[5] == 1'b1) && (out[7:6] === in[7:6]) && (out[4:0] === in[4:0])
    );
    // If highest set bit is 96, out[4] is forced high and others pass through.
    out_follows_priority_96: assert property (
        @(posedge clk) (!shifted_data[99] && !shifted_data[98] && !shifted_data[97] && shifted_data[96]) |-> (out[4] == 1'b1) && (out[7:5] === in[7:5]) && (out[3:0] === in[3:0])
    );
    // If highest set bit is 95, out[3] is forced high and others pass through.
    out_follows_priority_95: assert property (
        @(posedge clk) (!shifted_data[99] && !shifted_data[98] && !shifted_data[97] && !shifted_data[96] && shifted_data[95]) |-> (out[3] == 1'b1) && (out[7:4] === in[7:4]) && (out[2:0] === in[2:0])
    );
    // If highest set bit is 94, out[2] is forced high and others pass through.
    out_follows_priority_94: assert property (
        @(posedge clk) (!shifted_data[99] && !shifted_data[98] && !shifted_data[97] && !shifted_data[96] && !shifted_data[95] && shifted_data[94]) |-> (out[2] == 1'b1) && (out[7:3] === in[7:3]) && (out[1:0] === in[1:0])
    );
    // If highest set bit is 93, out[1] is forced high and others pass through.
    out_follows_priority_93: assert property (
        @(posedge clk) (!shifted_data[99] && !shifted_data[98] && !shifted_data[97] && !shifted_data[96] && !shifted_data[95] && !shifted_data[94] && shifted_data[93]) |-> (out[1] == 1'b1) && (out[7:2] === in[7:2]) && (out[0] === in[0])
    );
    // If highest set bit is 92, out[0] is forced high and others pass through.
    out_follows_priority_92: assert property (
        @(posedge clk) (!shifted_data[99] && !shifted_data[98] && !shifted_data[97] && !shifted_data[96] && !shifted_data[95] && !shifted_data[94] && !shifted_data[93] && shifted_data[92]) |-> (out[0] == 1'b1) && (out[7:1] === in[7:1])
    );
    // If none of bits 99:92 are set, out equals in.
    out_when_no_priority_bits: assert property (
        @(posedge clk) (|(shifted_data[99:92]) == 1'b0) |-> (out === in)
    );
    // out is always the bitwise OR of priority_encoded and in.
    out_equals_in_or_priority: assert property (
        @(posedge clk) (out === (in | priority_encoded))
    );
    // priority_encoded is one-hot or zero.
    priority_is_onehot_or_zero: assert property (
        @(posedge clk) $onehot0(priority_encoded)
    );
endmodule