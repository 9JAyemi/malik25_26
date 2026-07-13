module barrel_shifter_sva (
    input logic clk,
    input logic load,
    input logic [3:0] data,
    input logic [1:0] shift,
    input logic [3:0] result
);
    // Clock: clk (posedge). No reset in RTL.
    // Sequential: result updates on clk; load has priority; else shift by shift.

    // When load was HIGH last cycle, result now equals last cycle's data.
    load_captures_data: assert property (
        @(posedge clk) $past(load) |-> (result == $past(data))
    );

    // With no load and shift==00 last cycle, result holds its previous value.
    no_shift_holds: assert property (
        @(posedge clk) $past(!load && (shift == 2'b00)) |-> (result == $past(result))
    );

    // With no load and shift==01 last cycle, result = {old result[2:0], old data[3]}.
    shift_left_by_1: assert property (
        @(posedge clk) $past(!load && (shift == 2'b01)) |-> (result == {$past(result[2:0]), $past(data[3])})
    );

    // With no load and shift==10 last cycle, result = {old data[0], old result[3:1]}.
    shift_right_by_1: assert property (
        @(posedge clk) $past(!load && (shift == 2'b10)) |-> (result == {$past(data[0]), $past(result[3:1])})
    );

    // With no load and shift==11 last cycle, result = {old data[1:0], old result[3:2]}.
    shift_right_by_2: assert property (
        @(posedge clk) $past(!load && (shift == 2'b11)) |-> (result == {$past(data[1:0]), $past(result[3:2])})
    );

    // Bit check for shift==01: upper three bits move down by one.
    shift_left_by_1_upper_bits: assert property (
        @(posedge clk) $past(!load && (shift == 2'b01)) |-> (result[3:1] == $past(result[2:0]))
    );

    // Bit check for shift==01: LSB comes from data[3].
    shift_left_by_1_lsb_from_data3: assert property (
        @(posedge clk) $past(!load && (shift == 2'b01)) |-> (result[0] == $past(data[3]))
    );

    // Bit check for shift==10: MSB comes from data[0].
    shift_right_by_1_msb_from_data0: assert property (
        @(posedge clk) $past(!load && (shift == 2'b10)) |-> (result[3] == $past(data[0]))
    );

    // Bit check for shift==11: top two bits come from data[1:0].
    shift_right_by_2_top_from_data10: assert property (
        @(posedge clk) $past(!load && (shift == 2'b11)) |-> (result[3:2] == $past(data[1:0]))
    );
endmodule